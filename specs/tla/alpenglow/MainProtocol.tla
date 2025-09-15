---------------------------- MODULE MainProtocol ----------------------------
(***************************************************************************
 * MAIN ALPENGLOW CONSENSUS PROTOCOL SPECIFICATION
 * 
 * This is the top-level specification that combines all components and
 * defines the complete system behavior, including multiple validators,
 * Byzantine fault tolerance, and safety/liveness properties.
 * 
 * WHAT WE'RE PROVING:
 * - Safety (Theorem 1): No conflicting finalization
 * - Liveness (Theorem 2): Progress under synchrony
 * - Byzantine tolerance: Safe with <20% Byzantine stake
 * 
 * STRUCTURE:
 * 1. System state (validators, blocks, messages)
 * 2. Actions (how state changes)
 * 3. Safety invariants (what must always be true)
 * 4. Liveness properties (what must eventually happen)
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC,
        Messages, Blocks,
        Certificates, VoteStorage,
        VotorCore

\* ============================================================================
\* CONSTANTS
\* ============================================================================

CONSTANTS
    NumValidators,      \* Number of validators (e.g., 4 for testing)
    ByzantineCount,     \* Number of Byzantine validators (< 20% of stake)
    GST,                \* Global Stabilization Time
    MaxSlot,            \* Maximum slot for bounded model checking
    MaxBlocks           \* Maximum blocks for bounded model checking

ASSUME
    /\ NumValidators \in Nat \ {0}
    /\ ByzantineCount \in Nat
    /\ ByzantineCount < NumValidators
    /\ GST \in Nat
    /\ MaxSlot \in Nat \ {0}
    /\ MaxBlocks \in Nat \ {0}

\* ============================================================================
\* SYSTEM STATE VARIABLES
\* ============================================================================

VARIABLES
    validators,         \* Map: Validators -> ValidatorState
    blocks,             \* Set of all blocks in the system
    messages,           \* Set of messages in transit
    byzantineNodes,     \* Set of Byzantine validator IDs
    time,               \* Global time (for modeling synchrony)
    finalized           \* Map: Validators -> Set of finalized blocks

vars == <<validators, blocks, messages, byzantineNodes, time, finalized>>

\* ============================================================================
\* HELPER FUNCTIONS
\* ============================================================================

\* Get correct (non-Byzantine) validators
CorrectNodes == Validators \ byzantineNodes

\* Check if we're after GST (network is stable)
AfterGST == time >= GST

\* Calculate total Byzantine stake
ByzantineStake ==
    LET byzVals == byzantineNodes
    IN CalculateStake(byzVals)

\* Check Byzantine stake is less than 20%
ByzantineStakeOK ==
    ByzantineStake * 100 < TotalStake * 20

\* ============================================================================
\* INITIAL STATE
\* ============================================================================

Init ==
    /\ validators = [v \in Validators |-> AddState(InitValidatorState(v), 1, "ParentReady")]
    /\ blocks = {GenesisBlock}
    /\ messages = {}
    /\ byzantineNodes = IF ByzantineCount = 0 THEN {}
                        ELSE CHOOSE S \in SUBSET Validators : 
                             Cardinality(S) = ByzantineCount
    /\ ByzantineStakeOK
    /\ time = 0
    /\ finalized = [v \in Validators |-> {}]

\* ============================================================================
\* ACTIONS (State Transitions)
\* ============================================================================

(***************************************************************************
 * RECEIVE BLOCK
 * When: Validator receives a block
 * Effect: Process it according to voting rules
 ***************************************************************************)
ReceiveBlock(v, block) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ validators' = [validators EXCEPT ![v] = HandleBlock(validators[v], block)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * PROCESS TIMEOUT
 * When: Slot timeout expires
 * Effect: Vote to skip the slot
 ***************************************************************************)
ProcessTimeout(v, slot) ==
    /\ v \in CorrectNodes
    /\ slot \in Slots
    /\ slot <= MaxSlot
    /\ validators' = [validators EXCEPT ![v] = HandleTimeout(validators[v], slot)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * GENERATE CERTIFICATE
 * When: Enough votes collected
 * Effect: Create and broadcast certificate
 ***************************************************************************)
GenerateCertificateAction(v, slot) ==
    /\ v \in CorrectNodes
    /\ slot \in Slots
    /\ slot <= MaxSlot
    /\ LET pool == validators[v].pool
           certs == GenerateCertificate(pool, slot)
       IN /\ certs # {}
          /\ LET cert == CHOOSE c \in certs : TRUE
             IN /\ messages' = messages \union {cert}
                /\ validators' = [validators EXCEPT ![v].pool = StoreCertificate(validators[v].pool, cert)]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized>>

(***************************************************************************
 * FINALIZE BLOCK
 * When: Sufficient certificates exist
 * Effect: Mark block as finalized
 ***************************************************************************)
FinalizeBlock(v, block) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ LET pool == validators[v].pool
           slot == block.slot
       IN \/ HasFastFinalizationCert(pool, slot, block.hash)
          \/ (HasNotarizationCert(pool, slot, block.hash) /\ 
              HasFinalizationCert(pool, slot))
    /\ finalized' = [finalized EXCEPT ![v] = finalized[v] \union {block}]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time>>

(***************************************************************************
 * BYZANTINE ACTION
 * When: Byzantine validator acts
 * Effect: Can send arbitrary votes (equivocation)
 ***************************************************************************)
ByzantineAction(v) ==
    /\ v \in byzantineNodes
    /\ \E vote \in Vote : 
        /\ IsValidVote(vote)
        /\ vote.validator = v
        /\ messages' = messages \union {vote}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, time, finalized>>

(***************************************************************************
 * PROPOSE BLOCK
 * When: Leader's turn to propose
 * Effect: Add new block to system
 ***************************************************************************)
ProposeBlock(leader, slot, parent) ==
    /\ leader = Leader(slot)
    /\ leader \in CorrectNodes
    /\ parent \in blocks
    /\ slot > parent.slot
    /\ slot <= MaxSlot
    /\ Cardinality(blocks) < MaxBlocks
    /\ LET newBlock == [
           slot |-> slot,
           hash |-> CHOOSE h \in BlockHashes : 
                    h \notin {b.hash : b \in blocks},
           parent |-> parent.hash,
           leader |-> leader
       ]
       IN /\ blocks' = blocks \union {newBlock}
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * ADVANCE TIME
 * When: Time progresses
 * Effect: Update clocks and check timeouts
 ***************************************************************************)
AdvanceTime ==
    /\ time' = time + 1
    /\ validators' = [w \in Validators |->
                        IF w \in CorrectNodes
                        THEN AdvanceClock(validators[w], time')
                        ELSE validators[w]]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, finalized>>

(***************************************************************************
 * DELIVER VOTE
 * When: A vote exists in the message set
 * Effect: Store the vote in every validator's pool and remove from messages
 ***************************************************************************)
DeliverVote ==
    /\ \E vote \in messages : vote \in Vote
    /\ LET vmsg == CHOOSE vv \in messages : vv \in Vote
       IN /\ messages' = messages \ {vmsg}
          /\ validators' = [w \in Validators |->
                               [validators[w] EXCEPT
                                   !.pool = StoreVote(@, vmsg)]]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized>>

(***************************************************************************
 * DELIVER CERTIFICATE
 * When: A certificate exists in the message set
 * Effect: Store the certificate in every validator's pool and remove it
 ***************************************************************************)
DeliverCertificate ==
    /\ \E cert \in messages : cert \in Certificate
    /\ LET cmsg == CHOOSE cc \in messages : cc \in Certificate
       IN /\ messages' = messages \ {cmsg}
          /\ validators' = [w \in Validators |->
                               [validators[w] EXCEPT
                                   !.pool = StoreCertificate(@, cmsg)]]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized>>

(***************************************************************************
 * BROADCAST LOCAL VOTE
 * When: A validator has cast a vote locally
 * Effect: Enqueue that vote into the network messages for dissemination
 ***************************************************************************)
BroadcastLocalVote ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot :
         LET localVotes == validators[v].pool.votes[s][v]
         IN localVotes # {}
    /\ LET vSel == CHOOSE vv \in CorrectNodes :
                      \E s \in 1..MaxSlot : validators[vv].pool.votes[s][vv] # {}
           sSel == CHOOSE ss \in 1..MaxSlot : validators[vSel].pool.votes[ss][vSel] # {}
           vt == CHOOSE x \in validators[vSel].pool.votes[sSel][vSel] : TRUE
       IN messages' = messages \union {vt}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, time, finalized>>

(***************************************************************************
 * EVENT: BLOCK NOTARIZED
 * When: Pool has a notarization certificate for a block
 * Effect: Set BlockNotarized state and try to cast FinalVote
 ***************************************************************************)
EmitBlockNotarized ==
    /\ \E v \in CorrectNodes, b \in blocks :
         /\ b.slot \in 1..MaxSlot
         /\ ShouldEmitBlockNotarized(validators[v].pool, b.slot, b.hash)
         /\ validators' = [validators EXCEPT ![v] =
                               HandleBlockNotarized(@, b.slot, b.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * EVENT: SAFE TO NOTAR (fallback)
 * When: SafeToNotar predicate holds for a block we didn't initially vote for
 * Effect: TrySkipWindow and cast NotarFallbackVote
 ***************************************************************************)
EmitSafeToNotar ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, b \in blocks :
         /\ b.slot = s
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedForB == VotedForBlock(validators[v], s, b.hash)
            IN CanEmitSafeToNotar(validators[v].pool, s, b.hash, alreadyVoted, votedForB)
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToNotar(@, s, b.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * EVENT: SAFE TO SKIP (fallback)
 * When: SafeToSkip predicate holds for a slot we haven't skipped
 * Effect: TrySkipWindow and cast SkipFallbackVote
 ***************************************************************************)
EmitSafeToSkip ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot :
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedSkip == 
                    \E vt \in GetVotesForSlot(validators[v].pool, s) :
                        /\ vt.validator = v
                        /\ vt.type = "SkipVote"
            IN CanEmitSafeToSkip(validators[v].pool, s, alreadyVoted, votedSkip)
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToSkip(@, s)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * EVENT: PARENT READY
 * When: First slot of a window and prior slot is certified (and gaps skipped)
 * Effect: Set ParentReady and schedule timeouts for the window
 ***************************************************************************)
EmitParentReady ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, p \in blocks :
         /\ IsFirstSlotOfWindow(s)
         /\ p.slot + 1 = s
         /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)
         /\ validators' = [validators EXCEPT ![v] = HandleParentReady(@, s, p.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized>>

\* ============================================================================
\* NEXT STATE RELATION
\* ============================================================================

Next ==
    \/ \E v \in Validators, b \in blocks : ReceiveBlock(v, b)
    \/ \E v \in Validators, s \in 1..MaxSlot : ProcessTimeout(v, s)
    \/ \E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s)
    \/ \E v \in Validators, b \in blocks : FinalizeBlock(v, b)
    \/ \E v \in byzantineNodes : ByzantineAction(v)
    \/ \E l \in Validators, s \in 1..MaxSlot, p \in blocks : ProposeBlock(l, s, p)
    \/ DeliverVote
    \/ DeliverCertificate
    \/ BroadcastLocalVote
    \/ AdvanceTime

\* ============================================================================
\* SPECIFICATION
\* ============================================================================

\* Fairness: Ensure progress
Fairness ==
    /\ WF_vars(AdvanceTime)
    /\ WF_vars(DeliverVote)
    /\ WF_vars(DeliverCertificate)
    /\ WF_vars(BroadcastLocalVote)
    /\ WF_vars(\E l \in Validators, s \in 1..MaxSlot, p \in blocks : ProposeBlock(l, s, p))
    /\ WF_vars(\E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s))
    /\ \A v \in CorrectNodes : WF_vars(\E b \in blocks : ReceiveBlock(v, b))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ============================================================================
\* SAFETY PROPERTIES
\* ============================================================================

(***************************************************************************
 * MAIN SAFETY INVARIANT (Theorem 1 from whitepaper)
 * If two correct nodes finalize blocks, they must be in the same chain
 ***************************************************************************)
SafetyInvariant ==
    \A v1, v2 \in CorrectNodes :
    \A b1 \in finalized[v1], b2 \in finalized[v2] :
        (b1.slot <= b2.slot) => IsAncestor(b1, b2, blocks)

(***************************************************************************
 * LEMMA 20: Vote uniqueness
 * Correct nodes cast at most one initial vote per slot
 ***************************************************************************)
VoteUniqueness ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET votes == GetVotesForSlot(validators[v].pool, slot)
            initVotes == {vt \in votes : 
                         IsInitialVote(vt) /\ vt.validator = v}
        IN Cardinality(initVotes) <= 1

(***************************************************************************
 * LEMMA 24: Unique notarization
 * At most one block can be notarized per slot
 ***************************************************************************)
UniqueNotarization ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET pool == validators[v].pool
            notarCerts == {c \in pool.certificates[slot] : 
                          c.type = "NotarizationCert"}
            notarBlocks == {c.blockHash : c \in notarCerts}
        IN Cardinality(notarBlocks) <= 1

(***************************************************************************
 * LEMMA 25: Finalized implies notarized
 * Every finalized block was first notarized
 ***************************************************************************)
FinalizedImpliesNotarized ==
    \A v \in CorrectNodes :
    \A b \in finalized[v] :
        LET pool == validators[v].pool
        IN \E cert \in pool.certificates[b.slot] :
            /\ cert.type \in {"NotarizationCert", "FastFinalizationCert"}
            /\ cert.blockHash = b.hash

(***************************************************************************
 * No conflicting certificates
 * Can't have certificates for different blocks in same slot
 ***************************************************************************)
NoConflictingCerts ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET pool == validators[v].pool
        IN \A c1, c2 \in pool.certificates[slot] :
            (c1.type = c2.type /\ 
             c1.type \in {"NotarizationCert", "NotarFallbackCert"}) =>
            c1.blockHash = c2.blockHash

\* ============================================================================
\* LIVENESS PROPERTIES (Temporal)
\* ============================================================================

(***************************************************************************
 * EVENTUAL FINALIZATION
 * After GST, blocks eventually get finalized
 ***************************************************************************)
EventualFinalization ==
    (time >= GST) ~> 
        (\E v \in CorrectNodes :
         \E b \in blocks :
            b.slot > 0 /\ b \in finalized[v])

(***************************************************************************
 * PROGRESS
 * The highest finalized slot keeps increasing
 ***************************************************************************)
Progress ==
    (time >= GST) ~>
        (\A v \in CorrectNodes :
         LET currentMax == IF finalized[v] = {} THEN 0
                          ELSE CHOOSE s \in {b.slot : b \in finalized[v]} :
                               \A s2 \in {b.slot : b \in finalized[v]} : s >= s2
         IN \E b \in blocks : b.slot > currentMax /\ <>(b \in finalized[v]))

\* ============================================================================
\* TYPE INVARIANT
\* ============================================================================

TypeInvariant ==
    /\ validators \in [Validators -> ValidatorState]
    /\ blocks \subseteq Block
    /\ messages \subseteq (Vote \union Certificate)
    /\ byzantineNodes \subseteq Validators
    /\ time \in Nat
    /\ finalized \in [Validators -> SUBSET blocks]
    /\ \A v \in Validators : ValidatorStateOK(validators[v])

\* ============================================================================
\* MAIN INVARIANT (Combines all safety properties)
\* ============================================================================

Invariant ==
    /\ TypeInvariant
    /\ SafetyInvariant
    /\ VoteUniqueness
    /\ UniqueNotarization
    /\ FinalizedImpliesNotarized
    /\ NoConflictingCerts
    /\ ByzantineStakeOK

\* ============================================================================
\* STATE CONSTRAINTS (For bounded model checking)
\* ============================================================================

StateConstraint ==
    /\ Cardinality(blocks) <= MaxBlocks
    /\ time <= GST + 10
    /\ \A v \in Validators :
       \A s \in 1..MaxSlot :
           Cardinality(GetVotesForSlot(validators[v].pool, s)) <= NumValidators * 5

=============================================================================
