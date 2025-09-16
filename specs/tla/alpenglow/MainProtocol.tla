---------------------------- MODULE MainProtocol ----------------------------
(***************************************************************************
 * MAIN ALPENGLOW CONSENSUS PROTOCOL SPECIFICATION
 *
 * This is the “glue” module: it combines the data model and Votor logic
 * into a full protocol, following the order of presentation in Whitepaper
 * §2. Readers can match each action to the narrative:
 *   • §2.3 Blokstor events (`ReceiveBlock`, `EmitParentReady`, ...)
 *   • §2.4 Voting actions (`ProcessTimeout`, `GenerateCertificate`, ...)
 *   • §2.9 Safety invariants (Theorem 1) and §2.10 Liveness (Theorem 2)
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC,
        Messages, Blocks,
        Certificates, VoteStorage,
        VotorCore, Rotor

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
    finalized,          \* Map: Validators -> Set of finalized blocks
    blockAvailability   \* Map: Validators -> Set of reconstructed blocks

vars == <<validators, blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

\* ============================================================================
\* HELPER FUNCTIONS
\* ============================================================================

\* Get correct (non-Byzantine) validators
CorrectNodes == Validators \ byzantineNodes

\* Relays chosen by Rotor that are correct
RotorCorrectRelays(relays) == relays \cap CorrectNodes

\* Definition 6 (§2.2): Rotor succeeds if at least \gamma correct relays participate
EnoughCorrectRelays(relays) == Cardinality(RotorCorrectRelays(relays)) >= RotorGamma

\* Definition 19 & Algorithm 4: certificates prompting block repair
NeedsBlockRepair(pool, block) ==
    LET slot == block.slot
        hash == block.hash
    IN HasNotarizationCert(pool, slot, hash) \/ HasNotarFallbackCert(pool, slot, hash)

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
    /\ validators = [v \in Validators |->
                        LET base == InitValidatorState(v)
                            withParent == [base EXCEPT !.parentReady[1] = GenesisHash]
                        IN AddState(withParent, 1, "ParentReady")]
    /\ blocks = {GenesisBlock}
    /\ messages = {}
    /\ byzantineNodes = IF ByzantineCount = 0 THEN {}
                        ELSE CHOOSE S \in SUBSET Validators : 
                             Cardinality(S) = ByzantineCount
    /\ ByzantineStakeOK
    /\ time = 0
    /\ finalized = [v \in Validators |-> {}]
    /\ blockAvailability = [v \in Validators |-> {GenesisBlock}]

\* ============================================================================
\* ACTIONS (State Transitions)
\* ============================================================================

(***************************************************************************
 * RECEIVE BLOCK — Whitepaper Algorithm 1 (line 1 "Block")
 * Consume a Rotor-delivered block and invoke Votor's TRYNOTAR path.
 ***************************************************************************)
ReceiveBlock(v, block) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ block \in blockAvailability[v]
    /\ validators' = [validators EXCEPT ![v] = HandleBlock(validators[v], block)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * PROCESS TIMEOUT — Definition 17 & Algorithm 1 (line 6)
 * Fires when the scheduled deadline elapses, producing skip votes.
 ***************************************************************************)
ProcessTimeout(v, slot) ==
    /\ v \in CorrectNodes
    /\ slot \in Slots
    /\ slot <= MaxSlot
    /\ validators[v].timeouts[slot] > 0
    /\ time >= validators[v].timeouts[slot]
    /\ ~HasState(validators[v], slot, "Voted")
    /\ validators' = [validators EXCEPT ![v] = HandleTimeout(validators[v], slot)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * GENERATE CERTIFICATE — Definition 13 (certificate construction)
 * Aggregates qualifying votes and broadcasts the resulting certificate.
 ***************************************************************************)
GenerateCertificateAction(v, slot) ==
    /\ v \in CorrectNodes
    /\ slot \in Slots
    /\ slot <= MaxSlot
    /\ LET pool == validators[v].pool
           certs == GenerateCertificate(pool, slot)
           candidates == {c \in certs :
                             \/ c \notin messages
                             \/ (\E w \in Validators : CanStoreCertificate(validators[w].pool, c))}
       IN /\ candidates # {}
          /\ LET cert == CHOOSE c \in candidates : TRUE
             IN /\ messages' = messages \union {cert}
                /\ validators' = [validators EXCEPT ![v].pool = StoreCertificate(validators[v].pool, cert)]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * FINALIZE BLOCK — Definition 14 (fast vs slow finalization)
 * Finalizes on 80% fast certificates or 60% notar + final votes.
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
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, blockAvailability>>

(***************************************************************************
 * BYZANTINE ACTION — captures Assumption 1 adversarial behaviour
 * Allows arbitrary vote injection by validators flagged Byzantine.
 ***************************************************************************)
ByzantineAction(v) ==
    /\ v \in byzantineNodes
    /\ \E vote \in Vote : 
        /\ IsValidVote(vote)
        /\ vote.validator = v
        /\ messages' = messages \union {vote}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * HONEST PROPOSE BLOCK — Whitepaper §2.7 (Algorithm 3)
 * Correct leader builds a new block for its slot and stores it locally.
 ***************************************************************************)
HonestProposeBlock(leader, slot, parent) ==
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
          /\ blockAvailability' = [blockAvailability EXCEPT ![leader] = @ \union {newBlock}]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * BYZANTINE PROPOSE BLOCK — models equivocation/withholding by leaders
 * flagged Byzantine (§2.2, Example 44). They may mint multiple blocks for
 * the same slot and share them with any subset of validators.
 ***************************************************************************)
ByzantineProposeBlock(leader, slot, parent) ==
    /\ leader = Leader(slot)
    /\ leader \in byzantineNodes
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
          /\ \E targets \in SUBSET Validators :
                blockAvailability' =
                    [w \in Validators |->
                        IF w \in targets THEN blockAvailability[w] \union {newBlock}
                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * ADVANCE TIME — Implements the partial-synchrony model (§1.5, Def. 17)
 * Bumps global time and runs timeout processing on each validator.
 ***************************************************************************)
AdvanceTime ==
    /\ time' = time + 1
    /\ validators' = [w \in Validators |->
                        IF w \in CorrectNodes
                        THEN AdvanceClock(validators[w], time')
                        ELSE validators[w]]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, finalized, blockAvailability>>

(***************************************************************************
 * ROTOR DISSEMINATION (SUCCESS) — Whitepaper §2.2, Definition 6
 * Rotor succeeds once a correct leader samples ≥ γ correct relays.
 ***************************************************************************)
RotorDisseminateSuccess(block) ==
    /\ block \in blocks
    /\ block.leader \in CorrectNodes
    /\ LET needers == {v \in Validators : block \notin blockAvailability[v]}
           nextSlot == IF block.slot + 1 <= MaxSlot THEN block.slot + 1 ELSE block.slot
           nextLeader == Leader(nextSlot)
           relays == RotorSelect(block, needers, nextLeader)
       IN /\ needers # {}
          /\ relays # {}
          /\ EnoughCorrectRelays(relays)
          /\ blockAvailability' = [w \in Validators |-> blockAvailability[w] \union {block}]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * ROTOR DISSEMINATION (FAILURE) — Either the leader is Byzantine or fewer
 * than γ correct relays participate, so only the sampled relays learn the block.
 ***************************************************************************)
RotorDisseminateFailure(block) ==
    /\ block \in blocks
    /\ LET needers == {v \in Validators : block \notin blockAvailability[v]}
           nextSlot == IF block.slot + 1 <= MaxSlot THEN block.slot + 1 ELSE block.slot
           nextLeader == Leader(nextSlot)
           relays == RotorSelect(block, needers, nextLeader)
       IN /\ needers # {}
          /\ relays # {}
          /\ (block.leader \in byzantineNodes \/ ~EnoughCorrectRelays(relays))
          /\ blockAvailability' = [w \in Validators |->
                                        IF w \in relays
                                        THEN blockAvailability[w] \union {block}
                                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>


(***************************************************************************
 * REPAIR — Whitepaper §2.8 (Algorithm 4)
 * Fetch a notarized block from any node that already stores it.
 *************************************************************************)
RepairBlock(v, block, supplier) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ block \notin blockAvailability[v]
    /\ NeedsBlockRepair(validators[v].pool, block)
    /\ supplier \in Validators
    /\ block \in blockAvailability[supplier]
    /\ blockAvailability' = [blockAvailability EXCEPT ![v] = @ \union {block}]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>


(***************************************************************************
 * DELIVER VOTE — Dissemination layer for Definition 12 constraints
 * Removes a vote from the network set and stores it in each Pool.
 ***************************************************************************)
DeliverVote ==
    /\ \E vote \in messages : vote \in Vote
    /\ LET vmsg == CHOOSE vv \in messages : vv \in Vote
       IN /\ messages' = messages \ {vmsg}
          /\ validators' = [w \in Validators |->
                               [validators[w] EXCEPT
                                   !.pool = StoreVote(@, vmsg)]]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * DELIVER CERTIFICATE — Dissemination layer for Definition 13
 * Propagates certificates to every validator’s Pool.
 ***************************************************************************)
DeliverCertificate ==
    /\ \E cert \in messages : cert \in Certificate
    /\ LET cmsg == CHOOSE cc \in messages : cc \in Certificate
       IN /\ messages' = messages \ {cmsg}
          /\ validators' = [w \in Validators |->
                               [validators[w] EXCEPT
                                   !.pool = StoreCertificate(@, cmsg)]]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * BROADCAST LOCAL VOTE — pushes locally stored votes into the network
 * Ensures eventual delivery assumed in §2.4 (“broadcast to all other nodes”).
 ***************************************************************************)
BroadcastLocalVote ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot :
         LET localVotes == validators[v].pool.votes[s][v]
         IN localVotes # {}
    /\ LET vSel == CHOOSE vv \in CorrectNodes :
                      \E s \in 1..MaxSlot : validators[vv].pool.votes[s][vv] # {}
           sSel == CHOOSE ss \in 1..MaxSlot : validators[vSel].pool.votes[ss][vSel] # {}
           vt == CHOOSE x \in validators[vSel].pool.votes[sSel][vSel] : TRUE
       IN 
          /\ vt \notin messages
          /\ \E w \in Validators : vt \notin validators[w].pool.votes[vt.slot][vt.validator]
          /\ messages' = messages \union {vt}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * EVENT: BLOCK NOTARIZED — Definition 15
 * Emits `BlockNotarized` when the Pool holds a notarization certificate.
 ***************************************************************************)
EmitBlockNotarized ==
    /\ \E v \in CorrectNodes, b \in blocks :
         /\ b.slot \in 1..MaxSlot
         /\ ShouldEmitBlockNotarized(validators[v].pool, b.slot, b.hash)
         /\ validators' = [validators EXCEPT ![v] =
                               HandleBlockNotarized(@, b.slot, b.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * EVENT: SAFE TO NOTAR — Definition 16 (fallback branch)
 * Checks the fallback inequality and issues notar-fallback votes.
 ***************************************************************************)
EmitSafeToNotar ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, b \in blocks :
         /\ b.slot = s
         /\ b \in blockAvailability[v]
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedForB == VotedForBlock(validators[v], s, b.hash)
            IN CanEmitSafeToNotar(validators[v].pool, s, b.hash, b.parent, alreadyVoted, votedForB)
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToNotar(@, s, b.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * EVENT: SAFE TO SKIP — Definition 16 (skip branch)
 * Emits skip-fallback votes once the pooled skip stake is large enough.
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
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * EVENT: PARENT READY — Definition 15 (ParentReady signal)
 * Marks the first slot in a leader window when predecessors are certified.
 ***************************************************************************)
EmitParentReady ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, p \in blocks :
         /\ IsFirstSlotOfWindow(s)
         /\ p.slot + 1 = s
         /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)
         /\ validators' = [validators EXCEPT ![v] = HandleParentReady(@, s, p.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

\* ============================================================================
\* NEXT STATE RELATION
\* ============================================================================

Next ==
    \/ \E v \in Validators, b \in blocks : ReceiveBlock(v, b)
    \/ \E v \in Validators, s \in 1..MaxSlot : ProcessTimeout(v, s)
    \/ \E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s)
    \/ \E v \in Validators, b \in blocks : FinalizeBlock(v, b)
    \/ \E v \in byzantineNodes : ByzantineAction(v)
    \/ \E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p)
    \/ \E l \in Validators, s \in 1..MaxSlot, p \in blocks : ByzantineProposeBlock(l, s, p)
    \/ DeliverVote
    \/ DeliverCertificate
    \/ BroadcastLocalVote
    \/ \E b \in blocks : RotorDisseminateSuccess(b)
    \/ \E b \in blocks : RotorDisseminateFailure(b)
    \/ \E v \in Validators, b \in blocks, s \in Validators : RepairBlock(v, b, s)
    \/ AdvanceTime

\* ============================================================================
\* SPECIFICATION
\* ============================================================================

\* Fairness: Whitepaper §2.10 assumes that after GST, honest messages keep
\* flowing. These weak fairness annotations model that assumption for TLC.
Fairness ==
    /\ WF_vars(AdvanceTime)
    /\ WF_vars(DeliverVote)
    /\ WF_vars(DeliverCertificate)
    /\ WF_vars(BroadcastLocalVote)
    /\ WF_vars(\E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p))
    /\ WF_vars(\E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s))
    /\ WF_vars(\E b \in blocks : RotorDisseminateSuccess(b))
    /\ WF_vars(\E v \in Validators, b \in blocks, s \in Validators : RepairBlock(v, b, s))
    /\ \A v \in CorrectNodes : WF_vars(\E b \in blocks : ReceiveBlock(v, b))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ============================================================================
\* SAFETY PROPERTIES
\* ============================================================================

(***************************************************************************
 * MAIN SAFETY INVARIANT (Whitepaper §2.9, Theorem 1): finalized blocks form
 * a single chain of ancestry.
 ***************************************************************************)
SafetyInvariant ==
    \A v1, v2 \in CorrectNodes :
    \A b1 \in finalized[v1], b2 \in finalized[v2] :
        (b1.slot <= b2.slot) => IsAncestor(b1, b2, blocks)

(***************************************************************************
 * No conflicting finalization (Corollary of Theorem 1): if two validators
 * finalize blocks in the same slot, they must be identical.
 ***************************************************************************)
NoConflictingFinalization ==
    \A v1, v2 \in CorrectNodes :
    \A b1 \in finalized[v1], b2 \in finalized[v2] :
        (b1.slot = b2.slot) => b1.hash = b2.hash

(***************************************************************************
 * Chain consistency under <20% Byzantine stake — restates Theorem 1 using
 * the paper's resilience assumption (Assumption 1).
 ***************************************************************************)
ChainConsistency == SafetyInvariant

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
 * Certificate uniqueness / non-equivocation (Definition 13): validators
 * never assemble two certificates of the same type that point to different
 * blocks in the same slot.
 ***************************************************************************)
CertificateNonEquivocation ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET pool == validators[v].pool
        IN \A c1, c2 \in pool.certificates[slot] :
            (c1.type = c2.type /\ 
             c1.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}) =>
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
    /\ blockAvailability \in [Validators -> SUBSET blocks]
    /\ \A v \in Validators : ValidatorStateOK(validators[v])

\* ============================================================================
\* MAIN INVARIANT (Combines all safety properties)
\* ============================================================================

Invariant ==
    /\ TypeInvariant
    /\ SafetyInvariant
    /\ NoConflictingFinalization
    /\ ChainConsistency
    /\ VoteUniqueness
    /\ UniqueNotarization
    /\ FinalizedImpliesNotarized
    /\ CertificateNonEquivocation
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
