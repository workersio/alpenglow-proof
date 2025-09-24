---------------------------- MODULE MainProtocol ----------------------------
(***************************************************************************
 * MAIN ALPENGLOW CONSENSUS PROTOCOL SPECIFICATION
 *
 * This is the “glue” module: it combines the data model and Votor logic
 * into a full protocol, following the order of presentation in Whitepaper
 * §2. Readers can match each action to the narrative:
 *   • §2.3 Blokstor events (`ReceiveBlock`, `EmitParentReady`, ...)
 *   • §2.4 Voting actions and timeout handling
 *       (timeouts via `AdvanceTime` → `AdvanceClock`, `GenerateCertificate`, ...)
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
    /\ Cardinality(Validators) = NumValidators

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
EnoughCorrectRelays(leader, relays) == RotorSuccessful(leader, relays, CorrectNodes)

\* Definition 19 & Algorithm 4: certificates prompting block repair
\* Include fast-finalization cert to future-proof fast-only implementations.
NeedsBlockRepair(pool, block) ==
    LET slot == block.slot
        hash == block.hash
    IN HasFastFinalizationCert(pool, slot, hash)
       \/ HasNotarizationCert(pool, slot, hash)
       \/ HasNotarFallbackCert(pool, slot, hash)

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
    \* Genesis bootstrapping: slot 1 is considered ParentReady by fiat to seed
    \* the first leader window (consistent with Definition 15). This avoids
    \* requiring an explicit genesis certificate while preserving semantics.
    /\ blocks = {GenesisBlock}
    /\ messages = {}
    /\ byzantineNodes \in {S \in SUBSET Validators : Cardinality(S) = ByzantineCount}
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
 * Notes:
 * - Event exactness: model only the first Block(...) per slot per validator
 *   (whitepaper “first complete block”). Subsequent deliveries for the same
 *   slot are ignored via the BlockSeen flag.
 * - Broadcast decoupling: this action only updates local validator state;
 *   broadcasting of votes/certificates occurs in separate actions
 *   (BroadcastLocalVote, DeliverVote, DeliverCertificate).
 ***************************************************************************)
ReceiveBlock(v, block) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ IsValidBlock(block)
    /\ block \in blockAvailability[v]
    /\ ~HasState(validators[v], block.slot, "BlockSeen")
    /\ validators' = [validators EXCEPT ![v] =
                         AddState(HandleBlock(validators[v], block), block.slot, "BlockSeen")]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * GENERATE CERTIFICATE — Definition 13 (certificate construction)
 * Aggregates qualifying votes and broadcasts the resulting certificate.
 * Note: We broadcast if either (a) the certificate is new to `messages`
 * or (b) some validator can still store it in their Pool. This abstracts
 * the whitepaper's "store then broadcast" flow (Def. 13, p. 21).
 ***************************************************************************)
GenerateCertificateAction(v, slot) ==
    /\ v \in CorrectNodes
    /\ slot \in Slots
    /\ slot <= MaxSlot
    /\ LET pool == validators[v].pool
           certs == GenerateCertificate(pool, slot)
          candidates == {c \in certs :
                             /\ c \notin messages
                             /\ (\E w \in Validators : CanStoreCertificate(validators[w].pool, c))
                             /\ CanStoreCertificate(validators[v].pool, c)}
       IN /\ candidates # {}
          /\ LET cert ==
                    IF (\E c \in candidates : c.type = "NotarizationCert")
                    THEN CHOOSE c \in candidates : c.type = "NotarizationCert"
                    ELSE CHOOSE c \in candidates : TRUE
             IN /\ messages' = messages \union {cert}
                /\ validators' = [validators EXCEPT ![v].pool = StoreCertificate(validators[v].pool, cert)]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>

 (***************************************************************************
 * FINALIZE BLOCK — Definition 14 (fast vs slow finalization, p. 21)
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
 * BYZANTINE ACTION — captures Assumption 1 adversarial behaviour (Whitepaper §1.5)
 * Allows arbitrary vote injection by validators flagged Byzantine.
 ***************************************************************************)
ByzantineAction(v) ==
    /\ v \in byzantineNodes
    /\ \E vote \in Vote :
        /\ IsValidVote(vote)
        /\ vote.validator = v
        /\ vote.slot <= MaxSlot
        /\ messages' = messages \union {vote}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, time, finalized, blockAvailability>>

 (***************************************************************************
 * HONEST PROPOSE BLOCK (strict) — Whitepaper §2.7 (Algorithm 3)
 * Correct leader builds a new block for its slot and stores it locally.
 * For the first slot of a window, require ParentReady to have been emitted
 * (Def. 15, p. 21). This is a stricter gating than the optimistic variant.
 ***************************************************************************)
HonestProposeBlock(leader, slot, parent) ==
    /\ leader = Leader(slot)
    /\ leader \in CorrectNodes
    /\ parent \in blocks
    /\ slot \in Slots
    /\ slot > parent.slot
    /\ slot <= MaxSlot
    /\ Cardinality(blocks) < MaxBlocks
    \* Parent readiness discipline (Def. 15, p. 21) for first slots of windows.
    \* Genesis (slot = 1) is pre-initialised with ParentReady in Init.
    /\ IsFirstSlotOfWindow(slot)
        => HasState(validators[leader], slot, "ParentReady")
    /\ LET newBlock == [
           slot |-> slot,
           hash |-> CHOOSE h \in BlockHashes : 
                    h \notin {b.hash : b \in blocks},
           parent |-> parent.hash,
           leader |-> leader
       ]
       IN \* Hint: ExtendsChain(newBlock, blocks)
          /\ IsValidBlock(newBlock)
          /\ blocks' = blocks \union {newBlock}
          /\ blockAvailability' = [blockAvailability EXCEPT ![leader] = @ \union {newBlock}]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * HONEST PROPOSE BLOCK (optimistic) — Algorithm 3
 * Optional modeling variant: allow building at the first slot of a window
 * as soon as the ParentReady condition holds (without waiting for the
 * event state to be emitted). Disabled in Next by default — included here
 * for comparison with the strict gating variant above.
 ***************************************************************************)
HonestProposeBlockOptimistic(leader, slot, parent) ==
    /\ leader = Leader(slot)
    /\ leader \in CorrectNodes
    /\ parent \in blocks
    /\ slot \in Slots
    /\ slot > parent.slot
    /\ slot <= MaxSlot
    /\ Cardinality(blocks) < MaxBlocks
    \* Parent readiness check via predicate (Def. 15, p. 21) for first slots
    /\ IsFirstSlotOfWindow(slot)
        => ShouldEmitParentReady(validators[leader].pool, slot, parent.hash, parent.slot)
    /\ LET newBlock == [
           slot |-> slot,
           hash |-> CHOOSE h \in BlockHashes :
                    h \notin {b.hash : b \in blocks},
           parent |-> parent.hash,
           leader |-> leader
       ]
       IN /\ IsValidBlock(newBlock)
          /\ blocks' = blocks \union {newBlock}
          /\ blockAvailability' = [blockAvailability EXCEPT ![leader] = @ \union {newBlock}]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * BYZANTINE PROPOSE BLOCK — models equivocation/withholding by leaders
 * flagged Byzantine (Whitepaper §2.2, §2.7, Assumption 1). They may mint
 * multiple blocks for the same slot (equivocation) and share them with any
 * subset of validators (withholding, modeled via Blokstor in §2.3).
 ***************************************************************************)
ByzantineProposeBlock(leader, slot, parent) ==
    /\ leader = Leader(slot)
    /\ leader \in byzantineNodes
    /\ parent \in blocks
    /\ slot \in Slots
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
          /\ \E recipients \in SUBSET Validators :
                blockAvailability' =
                    [w \in Validators |->
                        IF w \in recipients THEN blockAvailability[w] \union {newBlock}
                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * ADVANCE TIME — Implements the partial-synchrony model (§1.5, Def. 17)
 * Bumps global time and runs timeout processing on each validator.
 * Only `CorrectNodes` advance their clocks, as Byzantine nodes are unconstrained
 * by the protocol rules and their behavior is modeled separately.
 *
 * Time model note (Def. 17): `time` is the absolute clock used to schedule
 * timeouts. `AdvanceTime` sets each correct validator's `clock := time'` and
 * calls `AdvanceClock`, so timeouts scheduled in `HandleParentReady` against
 * `validator.clock` are compared against the same global base.
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
 * Rotor succeeds once a correct leader samples ≥ γ correct relays (p. 20–22).
 * Note: On success, availability is updated for CorrectNodes only, aligning
 * with the whitepaper text ("all correct nodes will receive the block").
 ***************************************************************************)
RotorDisseminateSuccess(block) ==
    /\ block \in blocks
    /\ block.leader \in CorrectNodes
    /\ LET needers == {v \in Validators : block \notin blockAvailability[v]}
           \* Note: The ELSE-branch clamps at MaxSlot for bounded MC only;
           \* it has no direct protocol analogue (parameterization note).
           nextSlot == IF block.slot + 1 <= MaxSlot THEN block.slot + 1 ELSE block.slot
           nextLeader == Leader(nextSlot)
           relays == RotorSelect(block, needers, nextLeader)
       IN /\ needers # {}
          /\ relays # {}
          /\ RotorSuccessful(block.leader, relays, CorrectNodes)
          /\ SliceDelivered([leader |-> block.leader, needers |-> needers], relays, CorrectNodes)
          /\ blockAvailability' =
                [w \in Validators |->
                    IF w \in CorrectNodes
                    THEN blockAvailability[w] \union {block}
                    ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * ROTOR FAILURE (insufficient correct relays) — Definition 6 complement
 * Leader is correct but fewer than γ correct relays participate. Only
 * the selected relays learn the block. Recovery occurs via Repair (§2.8).
 ***************************************************************************)
RotorFailInsufficientRelays(block) ==
    /\ block \in blocks
    /\ block.leader \in CorrectNodes
    /\ LET needers == {v \in Validators : block \notin blockAvailability[v]}
           \* Note: The ELSE-branch clamps at MaxSlot for bounded MC only;
           \* it has no direct protocol analogue (parameterization note).
           nextSlot == IF block.slot + 1 <= MaxSlot THEN block.slot + 1 ELSE block.slot
           nextLeader == Leader(nextSlot)
           relays == RotorSelect(block, needers, nextLeader)
       IN /\ needers # {}
          /\ relays # {}
          /\ ~RotorSuccessful(block.leader, relays, CorrectNodes)
          /\ blockAvailability' = [w \in Validators |->
                                        IF w \in relays
                                        THEN blockAvailability[w] \union {block}
                                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * ROTOR FAILURE (Byzantine leader) — adversarial dissemination
 * Leader is Byzantine and may send shreds to any subset of validators,
 * unconstrained by PS-P selection. This can result in partial or no
 * dissemination. Recovery occurs via Repair (§2.8).
 ***************************************************************************)
RotorFailByzantineLeader(block) ==
    /\ block \in blocks
    /\ block.leader \in byzantineNodes
    /\ \E recipients \in SUBSET Validators :
          /\ blockAvailability' = [w \in Validators |->
                                        IF w \in recipients
                                        THEN blockAvailability[w] \union {block}
                                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * ROTOR NO-DISSEMINATION (Byzantine leader immediate fail)
 * Explicit no-op documenting the paper’s “immediate fail” case: a faulty
 * leader may send nothing at all in its dissemination round.
 ***************************************************************************)
RotorNoDissemination(block) ==
    /\ block \in blocks
    /\ block.leader \in byzantineNodes
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized, blockAvailability>>


(***************************************************************************
 * REPAIR — Whitepaper §2.8 (Algorithm 4)
 * Fetch a notarized block from any node that already stores it.
 *************************************************************************)
RepairBlock(v, block, supplier) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ block \notin blockAvailability[v]
    /\ NeedsBlockRepair(validators[v].pool, block)
    /\ supplier \in CorrectNodes
    /\ block \in blockAvailability[supplier]
    /\ blockAvailability' = [blockAvailability EXCEPT ![v] = @ \union {block}]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>


(***************************************************************************
 * DELIVER VOTE — Dissemination layer for Definition 12 constraints
 * Removes a vote from the network set and stores it in each Pool.
 ***************************************************************************)
DeliverVote ==
    /\ \E vote \in messages : vote \in Vote /\ IsValidVote(vote)
    /\ LET vmsg == CHOOSE vv \in messages : vv \in Vote /\ IsValidVote(vv)
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
    /\ \E cert \in messages : cert \in Certificate /\ IsValidCertificate(cert)
    /\ LET cmsg == CHOOSE cc \in messages : cc \in Certificate /\ IsValidCertificate(cc)
       IN /\ messages' = messages \ {cmsg}
          /\ validators' = [w \in Validators |->
                               [validators[w] EXCEPT
                                   !.pool = StoreCertificate(@, cmsg)]]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * BROADCAST LOCAL VOTE — pushes locally stored votes into the network
 * Ensures eventual delivery assumed in §2.4 (“broadcast to all other nodes”).
 * This action disseminates self-votes, modeling the “rebroadcast own votes”
 * guidance from §2.10 and the “broadcast ... vote” steps in Algorithms 1-2.
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
 * Emits `BlockNotarized` when the Pool holds a notarization certificate (p. 21).
 ***************************************************************************)
EmitBlockNotarized ==
    /\ \E v \in CorrectNodes, b \in blocks :
         /\ b.slot \in (Slots \cap 1..MaxSlot)
         /\ ShouldEmitBlockNotarized(validators[v].pool, b.slot, b.hash)
         /\ ~HasState(validators[v], b.slot, "BlockNotarized")
         /\ validators' = [validators EXCEPT ![v] =
                               HandleBlockNotarized(@, b.slot, b.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>> \* Finalization votes broadcasted by BroadcastLocalVote

 (***************************************************************************
 * EVENT: SAFE TO NOTAR — Definition 16 (fallback branch, p. 21)
 * Checks the fallback inequality and issues notar-fallback votes.
 * Formula: notar(b) ≥ 40% OR (skip(s)+notar(b) ≥ 60% AND notar(b) ≥ 20%).
 ***************************************************************************)
EmitSafeToNotar ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, b \in blocks :
         /\ b.slot = s
         /\ b \in blockAvailability[v]
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedForB == VotedForBlock(validators[v], s, b.hash)
            IN CanEmitSafeToNotar(validators[v].pool, s, b.hash, b.parent, alreadyVoted, votedForB)
         /\ ~HasState(validators[v], s, "BadWindow") \* Prevents re-emitting after a fallback vote was cast
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToNotar(@, s, b.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

 (***************************************************************************
 * EVENT: SAFE TO SKIP — Definition 16 (skip branch, p. 22)
 * Emits skip-fallback votes once the pooled skip stake is large enough.
 * Formula: skip(s) + Σ notar(b) − max notar(b) ≥ 40%.
 ***************************************************************************)
EmitSafeToSkip ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot :
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                \* Note: `SkipVote` refers to the initial skip vote (not skip-fallback).
                \* Repeated fallback emission is suppressed by the `BadWindow` guard below.
                votedSkip == 
                    \E vt \in GetVotesForSlot(validators[v].pool, s) :
                        /\ vt.validator = v
                        /\ vt.type = "SkipVote"
            IN CanEmitSafeToSkip(validators[v].pool, s, alreadyVoted, votedSkip)
         /\ ~HasSkipCert(validators[v].pool, s) \* Avoid redundant skip-fallback voting when skip cert already exists
         /\ ~HasState(validators[v], s, "BadWindow") \* Prevents re-emitting after a fallback vote was cast
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToSkip(@, s)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

 (***************************************************************************
 * EVENT: PARENT READY — Definition 15 (ParentReady signal, p. 21)
 * Marks the first slot in a leader window when predecessors are certified.
 ***************************************************************************)
EmitParentReady ==
    \* Note: The model assumes certificates refer to p \in blocks (consistent with 
    \* how votes and certs are created), clarifying why p is quantified from blocks.
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, p \in blocks :
         /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)
         /\ ~HasState(validators[v], s, "ParentReady")
         /\ validators' = [validators EXCEPT ![v] = HandleParentReady(@, s, p.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

\* ============================================================================
\* NEXT STATE RELATION
\* ============================================================================

Next ==
    \/ \E v \in Validators, b \in blocks : ReceiveBlock(v, b)
    \/ \E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s)
    \/ \E v \in Validators, b \in blocks : FinalizeBlock(v, b)
    \/ EmitBlockNotarized
    \/ EmitSafeToNotar
    \/ EmitSafeToSkip
    \/ EmitParentReady
    \/ \E v \in byzantineNodes : ByzantineAction(v)
    \* Note: `ProcessTimeout` is handled via `AdvanceTime` -> `AdvanceClock`.
    \* The optional optimistic proposer variant is defined as
    \* `HonestProposeBlockOptimistic` and not enabled by default.
    \/ \E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p)
    \/ \E l \in Validators, s \in 1..MaxSlot, p \in blocks : ByzantineProposeBlock(l, s, p)
    \/ DeliverVote
    \/ DeliverCertificate
    \/ BroadcastLocalVote
    \/ \E b \in blocks : RotorDisseminateSuccess(b)
    \/ \E b \in blocks : RotorFailInsufficientRelays(b)
    \/ \E b \in blocks : RotorFailByzantineLeader(b)
    \/ \E b \in blocks : RotorNoDissemination(b)
    \/ \E v \in Validators, b \in blocks, supplier \in Validators : RepairBlock(v, b, supplier)
    \/ AdvanceTime

\* ============================================================================
\* SPECIFICATION
\* ============================================================================

\* Fairness: Whitepaper §2.10 assumes that after GST, honest messages keep
\* flowing. The weak fairness conditions below are gated by `AfterGST` to
\* model post-GST eventual delivery/retransmission and scheduler fairness.
\* We also include finalization fairness to rule out starvation once enabled.
Fairness ==
    /\ WF_vars(AdvanceTime)
    /\ WF_vars(IF AfterGST THEN DeliverVote ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN DeliverCertificate ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN BroadcastLocalVote ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN EmitBlockNotarized ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN EmitSafeToNotar ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN EmitSafeToSkip ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN EmitParentReady ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p)) ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s)) ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E v \in Validators, b \in blocks : FinalizeBlock(v, b)) ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E b \in blocks : RotorDisseminateSuccess(b)) ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E v \in Validators, b \in blocks, supplier \in Validators : RepairBlock(v, b, supplier)) ELSE UNCHANGED vars)
    /\ \A v \in Validators :
           IF v \in CorrectNodes
           THEN WF_vars(IF AfterGST THEN (\E b \in blocks : ReceiveBlock(v, b)) ELSE UNCHANGED vars)
           ELSE TRUE

Spec == Init /\ [][Next]_vars /\ Fairness

\* ============================================================================
\* SAFETY PROPERTIES
\* ============================================================================

(***************************************************************************
 * MAIN SAFETY INVARIANT (Whitepaper §2.9, Theorem 1): finalized blocks form
 * a single chain of ancestry.
 *
 * Note: The equal-slot corollary (“if two correct nodes finalize at the
 * same slot, the blocks must be identical”) is captured separately by
 * NoConflictingFinalization for clarity, following the audit suggestion.
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
 * LEMMA 24 (global form): cross-validator notarization uniqueness
 * Both notarization and notar-fallback certificates agree on a block hash.
 *************************************************************************)
GlobalNotarizationUniqueness ==
    \A s \in 1..MaxSlot :
        \A v1, v2 \in CorrectNodes :
            LET p1 == validators[v1].pool
                p2 == validators[v2].pool
            IN \A c1 \in p1.certificates[s], c2 \in p2.certificates[s] :
                   (c1.type \in {"NotarizationCert", "NotarFallbackCert"} /\
                    c2.type \in {"NotarizationCert", "NotarFallbackCert"}) =>
                   c1.blockHash = c2.blockHash

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

(***************************************************************************
 * Honest non-equivocation (semantic constraint)
 * For any correct leader and any slot, there is at most one proposed block
 * with that (leader, slot) pair present in the global `blocks` set.
 ***************************************************************************)
HonestNonEquivocation ==
    \A l \in CorrectNodes :
    \A s \in 1..MaxSlot :
        LET bs == {b \in blocks : b.leader = l /\ b.slot = s}
        IN Cardinality(bs) <= 1

(***************************************************************************
 * TRANSIT CERTIFICATES VALID
 * All in-flight certificates are valid.
 ***************************************************************************)
TransitCertificatesValid ==
    \A c \in messages : c \in Certificate => IsValidCertificate(c)

\* Pool storage guarantees from Definitions 12–13 (white paper §2.5)
PoolMultiplicityOK ==
    \A v \in Validators : MultiplicityRulesRespected(validators[v].pool)

PoolCertificateUniqueness ==
    \A v \in Validators : CertificateUniqueness(validators[v].pool)

(*
 * Timeouts are never scheduled in the past.
 *)
TimeoutsInFuture ==
    \A v \in CorrectNodes:
        \A s \in 1..MaxSlot:
            LET timeout == validators[v].timeouts[s]
            IN timeout = 0 \/ timeout > validators[v].clock

(***************************************************************************
 * ROTOR SELECTION SOUNDNESS
 * Ensures RotorSelect always respects structural constraints when successful
 ***************************************************************************)
RotorSelectSoundness ==
    \A b \in blocks :
        LET needers == {v \in Validators : b \notin blockAvailability[v]}
            nextSlot == IF b.slot + 1 <= MaxSlot THEN b.slot + 1 ELSE b.slot
            nextLeader == Leader(nextSlot)
        IN RotorSelectSound(b, needers, nextLeader)

\* ============================================================================
\* LIVENESS PROPERTIES (Temporal)
\* ============================================================================

(***************************************************************************
 * BASIC LIVENESS (sanity check)
 * After GST, at least one non-genesis block is eventually finalized
 ***************************************************************************)
BasicLiveness ==
    (time >= GST) ~> 
        (\E v \in Validators :
             \E b \in blocks : b.slot > 0 /\ b \in finalized[v])

(***************************************************************************
 * PROGRESS
 * The highest finalized slot keeps increasing
 ***************************************************************************)
Progress ==
    (time >= GST) ~>
        (\A v \in Validators :
             LET currentMax == IF finalized[v] = {} THEN 0
                                 ELSE CHOOSE s \in {b.slot : b \in finalized[v]} :
                                          \A s2 \in {b.slot : b \in finalized[v]} : s >= s2
             IN <>(\E b \in blocks : b.slot > currentMax /\ b \in finalized[v]))

(***************************************************************************
 * THEOREM 2 (window-level liveness)
 * Under stated premises, every slot in the window gets finalized.
 *************************************************************************)
NoTimeoutsBeforeGST(startSlot) ==
    \A v \in CorrectNodes :
        \A i \in (WindowSlots(startSlot) \cap 1..MaxSlot) :
            validators[v].timeouts[i] = 0 \/ validators[v].timeouts[i] >= GST

WindowFinalizedState(s) ==
    \A v \in CorrectNodes :
        \A i \in (WindowSlots(s) \cap 1..MaxSlot) :
            \E b \in blocks :
                /\ b.slot = i
                /\ b.leader = Leader(s)
                /\ b \in finalized[v]

(*
 * Whitepaper Theorem 2 (Liveness), §2.10 p. 36:
 * Under the stated premises (correct window leader, no pre-GST timeouts,
 * and post-GST delivery/fairness), every slot in the leader’s window is
 * eventually finalized by all correct nodes.
 *)
WindowFinalization(s) ==
    (IsFirstSlotOfWindow(s) /\ Leader(s) \in CorrectNodes /\ NoTimeoutsBeforeGST(s) /\ time >= GST) ~>
        WindowFinalizedState(s)

\* Window liveness properties (if any) are defined in the MC harness.

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

(***************************************************************************
 * Implied invariant: if ParentReady is in the state, a certificate exists.
 * This is checked to catch regressions.
 ***************************************************************************)
ParentReadyImpliesCert ==
    \A v \in CorrectNodes, s \in 1..MaxSlot:
        (s > 1 /\ "ParentReady" \in validators[v].state[s]) =>
            \E p \in blocks:
                ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)

(***************************************************************************
 * Implied invariant: if BlockNotarized is in the state, a certificate exists.
 * This is checked to catch regressions.
 ***************************************************************************)
BlockNotarizedImpliesCert ==
    \A v \in CorrectNodes, s \in 1..MaxSlot :
        (\E b \in blocks : b.slot = s /\ "BlockNotarized" \in validators[v].state[s]) =>
        (\E b \in blocks : b.slot = s /\ HasNotarizationCert(validators[v].pool, s, b.hash))

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
    /\ GlobalNotarizationUniqueness
    /\ FinalizedImpliesNotarized
    /\ CertificateNonEquivocation
    /\ HonestNonEquivocation
    /\ TransitCertificatesValid
    /\ ByzantineStakeOK
    /\ PoolMultiplicityOK
    /\ PoolCertificateUniqueness
    /\ RotorSelectSoundness
    /\ TimeoutsInFuture
    /\ BlockNotarizedImpliesCert
    /\ ParentReadyImpliesCert

\* ============================================================================
\* STATE CONSTRAINTS (For bounded model checking)
\* ============================================================================

StateConstraint ==
    /\ Cardinality(blocks) <= MaxBlocks
    /\ time <= GST + 10
    /\ \A v \in Validators :
       \A s \in 1..MaxSlot :
           \* Sanity check: bound total votes stored per slot in a validator's pool 
           Cardinality(GetVotesForSlot(validators[v].pool, s)) <= NumValidators * 5

=============================================================================
