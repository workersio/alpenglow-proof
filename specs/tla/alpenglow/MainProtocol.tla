---------------------------- MODULE MainProtocol ----------------------------
(***************************************************************************
 * MAIN ALPENGLOW CONSENSUS PROTOCOL SPECIFICATION
 *
 * Purpose (high level)
 * - This module ties together the data model (blocks, messages, pools) and
 *   the Votor logic into a complete protocol, mirroring the whitepaper’s
 *   structure of Section 2 (Rotor → Blokstor → Votor → Safety/Liveness).
 *
 * Whitepaper references (section • key lines • page)
 * - Rotor success/failure (Definition 6): `alpenglow-whitepaper.md:414` • p.20–22
 *   Resilience note and “immediate fail”: `alpenglow-whitepaper.md:416` • p.20–22
 * - Blokstor emits Block(...): `alpenglow-whitepaper.md:468` • §2.3
 * - Votes & certificates overview: §2.4 at `alpenglow-whitepaper.md:474` • p.19–22
 *   • Definition 12 (storing votes): `alpenglow-whitepaper.md:513` • p.20–21
 *   • Definition 13 (certificates): `alpenglow-whitepaper.md:520` • p.20–21
 *   • Table 5/6 thresholds (80/60): see p.20 in the markdown (tables after 19)
 *   • Definition 14 (finalization): `alpenglow-whitepaper.md:536` • p.21
 *   • Definition 15 (Pool events): `alpenglow-whitepaper.md:543` • p.21
 *   • Definition 16 (fallback events + formulas): `alpenglow-whitepaper.md:554` • p.21–22
 *   • Definition 17 (timeouts): `alpenglow-whitepaper.md:607` and formula `:609` • p.23
 * - Votor algorithms: Algorithm 1 (event loop) `:634`, Algorithm 2 (helpers) `:676`,
 *   Algorithm 3 (block creation, optimistic) `:759` with overview text `:727`,
 *   Algorithm 4 (repair) `:801`.
 * - Safety (Theorem 1): §2.9 intro `:816`, statement `:930` • p.34–35
 * - Liveness (Theorem 2): §2.10 intro `:941`, statement `:1045` • p.36+
 * - Adversary and <20% Byzantine stake: Assumption 1 `:107`, model text `:226` • §1.5
 *
 * Reading guide
 * - Each section/action below starts with a brief explanation, explicit
 *   whitepaper references (file:line • section • page), assumptions, and
 *   any key formulas. The intent is readability without flipping back to
 *   the paper while keeping the math precise.
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

(***************************************************************************
 * Constants — model parameters and paper assumptions
 *
 * Whitepaper refs
 * - Fault tolerance <20% stake (Assumption 1): `alpenglow-whitepaper.md:107`, `:226` • §1.5
 * - GST/partial synchrony and timing: `alpenglow-whitepaper.md:230` (synchrony),
 *   timeouts/clock discussion `:224` • §1.5; timeout schedule `:607`, `:609` • p.23
 * - 80/60 thresholds context: p.19–21 (Tables 5–6 around `:474`–`:520`).
 *
 * Notes
 * - `GST` gates liveness/fairness in Spec after network stabilizes (§2.10).
 * - `MaxSlot`/`MaxBlocks` bound state space for model checking only (no direct
 *   whitepaper analogue).
 ***************************************************************************)

ASSUME
    /\ NumValidators \in Nat \ {0}
    /\ ByzantineCount \in Nat
    /\ ByzantineCount < NumValidators
    /\ GST \in Nat
    /\ MaxSlot \in Nat \ {0}
    /\ MaxBlocks \in Nat \ {0}
    /\ Cardinality(Validators) = NumValidators
    /\ Slots = 0..MaxSlot   \* Centralize epoch bound: finite slot domain (includes genesis slot 0)

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

(***************************************************************************
 * State variables — correspondence to the paper
 *
 * Whitepaper refs
 * - Blocks/Blokstor and Block(...) event: `alpenglow-whitepaper.md:468` • §2.3
 * - Votes/certificates/Pool: `:474` (intro), `:513` (Def.12), `:520` (Def.13) • p.19–21
 * - Finalization definition: `:536` (Def.14) • p.21
 * - Timeouts/clock model: `:224` (local clocks), `:607`–`:613` (Def.17) • p.23
 * - Adversary/byzantine set: `:107` (Assumption 1), `:226` (model) • §1.5
 *
 * Mapping
 * - `validators`: local Votor state incl. `pool`, `state`, `timeouts` (Alg.1–2).
 * - `blocks`: the set of known blocks (Blokstor storage) per §2.3.
 * - `messages`: in-flight votes/certificates (Tables 5–6; §2.4).
 * - `byzantineNodes`: nodes allowed arbitrary behavior (Assumption 1).
 * - `time`: global model time to drive Def.17-style timeouts uniformly.
 * - `finalized`: per-validator set of finalized blocks (Def.14).
 * - `blockAvailability`: which blocks each validator can reconstruct (Rotor/repair).
 ***************************************************************************)

\* ============================================================================
\* HELPER FUNCTIONS
\* ============================================================================

\* Get correct (non-Byzantine) validators
CorrectNodes == Validators \ byzantineNodes

\* Relays chosen by Rotor that are correct
RotorCorrectRelays(relays) == relays \cap CorrectNodes

\* Definition 6 (§2.2): Rotor succeeds if ≥ γ correct relays participate
EnoughCorrectRelays(leader, relays) == RotorSuccessful(leader, relays, CorrectNodes)

\* Repair trigger (Algorithm 4; §2.8). Include fast-finalization to cover fast-only
\* implementations. See also Blokstor repair mention: `alpenglow-whitepaper.md:470`.
NeedsBlockRepair(pool, block) ==
    LET slot == block.slot
        hash == block.hash
    IN HasFastFinalizationCert(pool, slot, hash)
       \/ HasNotarizationCert(pool, slot, hash)
       \/ HasNotarFallbackCert(pool, slot, hash)

\* Check if we're after GST (network is stable; §1.5/§2.10)
AfterGST == time >= GST

\* Calculate total Byzantine stake
ByzantineStake ==
    LET byzVals == byzantineNodes
    IN CalculateStake(byzVals)

\* Assumption 1: Byzantine stake < 20% of total (`alpenglow-whitepaper.md:107`)
ByzantineStakeOK ==
    ByzantineStake * 100 < TotalStake * 20

\* ============================================================================
\* INITIAL STATE
\* ============================================================================

(***************************************************************************
 * INITIAL STATE — bootstrapping genesis and validator state
 *
 * Whitepaper refs
 * - Pool events and ParentReady: `alpenglow-whitepaper.md:543`–`:546` (Def.15) • p.21
 * - One-window gating via ParentReady for the first slot of a window (Alg.1–2).
 *
 * Explanation
 * - We mark slot 1 as ParentReady by fiat to seed the first leader window,
 *   consistent with Def.15’s semantics without requiring an explicit genesis
 *   certificate. Each validator starts from `InitValidatorState` and records
 *   the genesis hash for slot 1 to allow the first proposer to proceed.
 *
 * Assumptions
 * - Byzantine stake < 20% (Assumption 1): `alpenglow-whitepaper.md:107`.
 ***************************************************************************)
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
 * RECEIVE BLOCK — Blokstor → Votor handoff (Algorithm 1)
 *
 * Whitepaper refs
 * - Blokstor emits Block(s, hash(b), hash(parent(b))): `alpenglow-whitepaper.md:468` • §2.3
 * - Algorithm 1, event loop: `alpenglow-whitepaper.md:634`.
 *
 * Explanation
 * - Consume a Rotor-delivered block and process it via Votor (TRYNOTAR path).
 *
 * Assumptions
 * - Only the first complete block per slot is delivered to Alg.1 (“first complete
 *   block”), modeled via the `BlockSeen` flag to ignore duplicates.
 * - Dissemination/broadcast of votes and certificates is decoupled and handled
 *   by separate actions (BroadcastLocalVote, DeliverVote, DeliverCertificate).
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
 * GENERATE CERTIFICATE — aggregate and broadcast (Definition 13)
 *
 * Whitepaper refs
 * - Certificates and broadcast-on-store: `alpenglow-whitepaper.md:520` (Def.13) • p.20–21
 *   • Single stored copy per type per slot/block: p.21 (immediately after `:520`).
 * - Thresholds (Table 6): p.20 (fast 80%, notar 60%, fallback 60%, skip 60%).
 *
 * Explanation
 * - Aggregate qualifying votes into a certificate and broadcast it if newly
 *   learned by any node (abstracting the “store then broadcast” rule).
 * - Prefer fast-finalization first, then notarization among candidates.
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
                    IF (\E c \in candidates : c.type = "FastFinalizationCert")
                    THEN CHOOSE c \in candidates : c.type = "FastFinalizationCert"
                    ELSE IF (\E c \in candidates : c.type = "NotarizationCert")
                         THEN CHOOSE c \in candidates : c.type = "NotarizationCert"
                         ELSE CHOOSE c \in candidates : TRUE
             IN /\ messages' = messages \union {cert}
                /\ validators' = [validators EXCEPT ![v].pool = StoreCertificate(validators[v].pool, cert)]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>

(***************************************************************************
 * FINALIZE BLOCK — fast vs slow (Definition 14)
 *
 * Whitepaper refs
 * - Finalization modes: `alpenglow-whitepaper.md:536` (Def.14) • p.21
 *   • Fast: Fast-FinalizationCert(b) → finalize b.
 *   • Slow: FinalizationCert(s) + NotarizationCert(s, b) → finalize b in slot s.
 *
 * Explanation
 * - Finalize block `b` if either an 80% fast-finalization cert exists, or a 60%
 *   notarization cert exists together with a 60% finalization cert for the slot.
 ***************************************************************************)
FinalizeBlock(v, block) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ LET pool == validators[v].pool
           slot == block.slot
       IN \/ HasFastFinalizationCert(pool, slot, block.hash)
          \/ CanFinalizeSlow(pool, slot, block.hash)
    /\ finalized' = [finalized EXCEPT ![v] = finalized[v] \union GetAncestors(block, blocks)]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, blockAvailability>>

(***************************************************************************
 * BYZANTINE ACTION — adversary can inject arbitrary votes
 *
 * Whitepaper refs
 * - Assumption 1 (<20% byzantine stake): `alpenglow-whitepaper.md:107`.
 * - Adversary model narrative: `alpenglow-whitepaper.md:226` • §1.5.
 *
 * Explanation
 * - Byzantine validators may create and inject arbitrary valid-looking votes.
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
 * HONEST PROPOSE BLOCK (strict) — Algorithm 3 with ParentReady gating
 *
 * Whitepaper refs
 * - Algorithm 3 (block creation): `alpenglow-whitepaper.md:759`, overview `:727` • §2.7
 * - ParentReady (gating first slot of window): `:543`–`:546` (Def.15) • p.21.
 *
 * Explanation
 * - Correct leader for slot `s` creates a new block that extends `parent`.
 * - For the first slot of a window, require `ParentReady` to be in state,
 *   matching Def.15’s precondition for starting the window.
***************************************************************************)
\* Proposal is gated on leader having the parent locally (Rotor handoff).
HonestProposeBlock(leader, slot, parent) ==
    /\ leader \in CorrectNodes
    /\ parent \in blocks
    /\ parent \in blockAvailability[leader]
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
          /\ LeaderMatchesSchedule(newBlock)
          /\ IsValidBlock(newBlock)
          /\ blocks' = blocks \union {newBlock}
          /\ blockAvailability' = [blockAvailability EXCEPT ![leader] = @ \union {newBlock}]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * HONEST PROPOSE BLOCK (optimistic) — Algorithm 3 optimization
 *
 * Whitepaper refs
 * - Text on optimistic building: `alpenglow-whitepaper.md:727` • §2.7
 * - Algorithm 3: `:759`.
 *
 * Explanation
 * - Allow the leader to begin building at the first slot of a window as soon
 *   as the ParentReady predicate would hold (even before the event is emitted).
 * - Disabled by default; included for comparison with the strict variant.
***************************************************************************)
\* Optimistic proposal also requires having the parent locally (Rotor handoff).
HonestProposeBlockOptimistic(leader, slot, parent) ==
    /\ leader \in CorrectNodes
    /\ parent \in blocks
    /\ parent \in blockAvailability[leader]
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
       IN /\ LeaderMatchesSchedule(newBlock)
          /\ IsValidBlock(newBlock)
          /\ blocks' = blocks \union {newBlock}
          /\ blockAvailability' = [blockAvailability EXCEPT ![leader] = @ \union {newBlock}]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * BYZANTINE PROPOSE BLOCK — equivocation/withholding by faulty leaders
 *
 * Whitepaper refs
 * - Rotor/Blokstor context and leader behavior: §2.2–§2.3 (see `:414`, `:468`).
 * - Assumption 1 (byzantine power): `alpenglow-whitepaper.md:107`.
 *
 * Explanation
 * - A faulty leader can create multiple blocks for the same slot (equivocation)
 *   and send them to arbitrary subsets of validators (withholding).
 ***************************************************************************)
ByzantineProposeBlock(leader, slot, parent) ==
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
       IN /\ LeaderMatchesSchedule(newBlock)
          /\ blocks' = blocks \union {newBlock}
          /\ \E recipients \in SUBSET Validators :
                blockAvailability' =
                    [w \in Validators |->
                        IF w \in recipients THEN blockAvailability[w] \union {newBlock}
                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * ADVANCE TIME — partial-synchrony timers (Definition 17)
 *
 * Whitepaper refs
 * - Local timeouts and no need for synchronized clocks: `alpenglow-whitepaper.md:224` • §1.5
 * - Timeout schedule (Def.17): `:607` with formula `:609` • p.23.
 *
 * Explanation
 * - Bump global model time and advance each correct validator’s local timers.
 * - Modeling choice: we use a single `time` to drive `validator.clock` for all
 *   correct nodes so Def.17-computed deadlines are comparable.
 ***************************************************************************)
AdvanceTime ==
    /\ time' = time + 1
    /\ validators' = [w \in Validators |->
                        IF w \in CorrectNodes
                        THEN AdvanceClock(validators[w], time')
                        ELSE validators[w]]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, finalized, blockAvailability>>

(***************************************************************************
 * ROTOR DISSEMINATION (SUCCESS) — distribute to all correct nodes
 *
 * Whitepaper refs
 * - Definition 6 (Rotor success): `alpenglow-whitepaper.md:414` • §2.2, p.20–22
 *   Resilience text (“all correct nodes will receive the block”): `:416`.
 *
 * Explanation
 * - If a correct leader samples ≥ γ correct relays, all correct nodes reconstruct
 *   the block. We update availability only for `CorrectNodes` accordingly.
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
          \* SliceDelivered abstracts block-level dissemination once γ correct relays
          \* participate; use as the single success gate (drops redundant RotorSuccessful).
          /\ SliceDelivered([leader |-> block.leader, needers |-> needers], relays, CorrectNodes)
          /\ blockAvailability' =
                [w \in Validators |->
                    IF w \in CorrectNodes
                    THEN blockAvailability[w] \union {block}
                    ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>

(***************************************************************************
 * ROTOR FAILURE (insufficient correct relays) — partial dissemination
 *
 * Whitepaper refs
 * - Complement of Definition 6 (failure path): `alpenglow-whitepaper.md:414`.
 * - Repair mechanism: `:801` (Algorithm 4) and Blokstor repair note `:470`.
 *
 * Explanation
 * - Leader is correct, but fewer than γ correct relays participate; only selected
 *   relays receive the block. Recovery happens via repair (§2.8).
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
 * ROTOR FAILURE (Byzantine leader) — arbitrary dissemination/withholding
 *
 * Whitepaper refs
 * - Adversarial behavior permitted (Assumption 1/model): `alpenglow-whitepaper.md:226`.
 * - Repair (§2.8): `:801`.
 *
 * Explanation
 * - A faulty leader may disseminate to an arbitrary subset or to nobody at all.
 *   Correct nodes recover via repair.
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
 * ROTOR NO-DISSEMINATION — immediate fail case
 *
 * Whitepaper refs
 * - “Immediate fail” scenario: `alpenglow-whitepaper.md:416` (resilience note).
 *
 * Explanation
 * - No-op capturing a Byzantine leader sending nothing in its round.
 ***************************************************************************)
RotorNoDissemination(block) ==
    /\ block \in blocks
    /\ block.leader \in byzantineNodes
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized, blockAvailability>>


(***************************************************************************
 * REPAIR — fetch missing notarized blocks (Algorithm 4)
 *
 * Whitepaper refs
 * - Algorithm 4 (Repair): `alpenglow-whitepaper.md:801` • §2.8
 * - Blokstor repair obligation: `:470`.
 *
 * Explanation
 * - If Pool indicates a certificate implies a block should be present, fetch
 *   the notarized block from any correct node that already stores it.
 ***************************************************************************)
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
 * DELIVER VOTE — store received votes (Definition 12)
 *
 * Whitepaper refs
 * - Definition 12 (storing votes per-slot/node with multiplicity caps):
 *   `alpenglow-whitepaper.md:513` • p.20–21.
 * - Algorithm 1 (event loop handles received votes): `:634`.
 *
 * Explanation
 * - Pop a vote from the network and store it in every validator’s Pool, honoring
 *   the storage/multiplicity rules of Def.12.
 * - Ingress contract (audit note): only well-typed and semantically valid
 *   votes are accepted from the network. Concretely, the guard requires
 *   `vote \in Vote /\ IsValidVote(vote)` when selecting from `messages`.
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
 * DELIVER CERTIFICATE — store and propagate (Definition 13)
 *
 * Whitepaper refs
 * - Definition 13 (generate/store/broadcast certificates): `alpenglow-whitepaper.md:520` • p.20–21.
 *
 * Explanation
 * - Pop a certificate and store it in every validator’s Pool.
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
 * BROADCAST LOCAL VOTE — ensure eventual delivery of own votes
 *
 * Whitepaper refs
 * - Broadcast semantics in the protocol model: `alpenglow-whitepaper.md:207`.
 * - Liveness/standstill retransmission guidance: `:1231` • §2.10.
 * - Algorithms 1–2 repeatedly broadcast votes upon handling events (see `:634`).
 *
 * Explanation
 * - Push locally stored votes into the network to ensure they eventually reach
 *   all nodes, matching the paper’s retransmit/broadcast guidance.
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
 * EVENT: BLOCK NOTARIZED — when Pool holds a notar cert
 *
 * Whitepaper refs
 * - Definition 15 (Pool events): `alpenglow-whitepaper.md:543` • p.21.
 *
 * Explanation
 * - Emit BlockNotarized(s, hash(b)) when a notarization certificate is present.
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
 * EVENT: SAFE TO NOTAR — fallback inequality (Definition 16)
 *
 * Whitepaper refs
 * - Definition 16 (SafeToNotar): `alpenglow-whitepaper.md:554`–`:556` • p.21–22.
 *   • Formula (page 22): notar(b) ≥ 40% OR (skip(s)+notar(b) ≥ 60% AND notar(b) ≥ 20%).
 *
 * Explanation
 * - When that inequality holds and the node hasn’t already voted to notarize b
 *   in slot s, emit the event and cast notar-fallback accordingly (Alg.1).
 * - We pass the full block `b` into the handler and use the typed wrapper
 *   to ensure slot–hash pairing by construction; creation occurs only under
 *   the CanEmitSafeToNotar guard above (aid to model checking).
 ***************************************************************************)
EmitSafeToNotar ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, b \in blocks :
         /\ b.slot = s
         /\ b \in blockAvailability[v]
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedForB == VotedForBlock(validators[v], s, b.hash)
            IN CanEmitSafeToNotar(validators[v].pool, s, b.hash, b.parent, alreadyVoted, votedForB)
         /\ ~HasState(validators[v], s, "BadWindow") \* Prevents re-emitting after a fallback vote was cast
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToNotar(@, b)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>

 (***************************************************************************
 * EVENT: SAFE TO SKIP — fallback inequality (Definition 16)
 *
 * Whitepaper refs
 * - Definition 16 (SafeToSkip): `alpenglow-whitepaper.md:571` • p.22.
 *   • Formula (page 22): skip(s) + Σ notar(b) − max_b notar(b) ≥ 40%.
 *
 * Explanation
 * - When that inequality holds and the node hasn’t already voted to skip s,
 *   emit SafeToSkip(s) and cast a skip-fallback vote (Alg.1).
 ***************************************************************************)
EmitSafeToSkip ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot :
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                \* Note: `SkipVote` refers to the initial skip vote (not skip-fallback).
                \* Repeated fallback emission is suppressed by the `BadWindow` guard below.
                \* Suppression rationale: Algorithm 1 (lines ~21–25) emits SafeToSkip
                \* at most once per window per node; Algorithm 2 (TRYSKIPWINDOW,
                \* lines ~22–27) sets BadWindow when any fallback or skip vote is
                \* cast. The guards here mirror that behaviour.
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
 * EVENT: PARENT READY — first slot of a leader window (Definition 15)
 *
 * Whitepaper refs
 * - Definition 15 (ParentReady): `alpenglow-whitepaper.md:543`–`:546` • p.21.
 *
 * Explanation
 * - Mark the first slot of a new leader window once predecessors are certified.
 ***************************************************************************)
EmitParentReady ==
    \* Note: The model assumes certificates refer to p \in blocks (consistent with 
    \* how votes and certs are created), clarifying why p is quantified from blocks.
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, p \in blocks :
         /\ p.slot < s  \* Only consider previous blocks as parents (Def. 15)
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

(*
 * FAIRNESS — liveness after GST assumes eventual delivery/scheduling
 *
 * Whitepaper refs
 * - Liveness section: `alpenglow-whitepaper.md:941`–`:1045` (Theorem 2).
 * - Practical retransmission (standstill): `:1216`, `:1231` • §2.10.
 *
 * Explanation
 * - After GST, weak fairness on delivery and event emission models the paper’s
 *   assumption that honest messages keep flowing and get scheduled.
 *)
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
 * MAIN SAFETY INVARIANT — finalized blocks form a single chain
 *
 * Whitepaper refs
 * - Theorem 1 (safety): `alpenglow-whitepaper.md:930` • §2.9.
 *
 * Explanation
 * - If a correct node finalizes b at slot s and some (later) correct node
 *   finalizes b' at slot s' ≥ s, then b' is a descendant of b.
 * - Equal-slot corollary captured by NoConflictingFinalization below.
 ***************************************************************************)
SafetyInvariant ==
    \A v1, v2 \in CorrectNodes :
    \A b1 \in finalized[v1], b2 \in finalized[v2] :
        (b1.slot <= b2.slot) => IsAncestor(b1, b2, blocks)

(***************************************************************************
 * NO CONFLICTING FINALIZATION — equal-slot corollary of Theorem 1
 *
 * Explanation
 * - If two correct validators finalize blocks in the same slot, those blocks
 *   must have identical hashes.
 ***************************************************************************)
NoConflictingFinalization ==
    \A v1, v2 \in CorrectNodes :
    \A b1 \in finalized[v1], b2 \in finalized[v2] :
        (b1.slot = b2.slot) => b1.hash = b2.hash

(***************************************************************************
 * SAFE-TO-SKIP PRECLUDES FAST — Def.16 ⇒ no 80% notar later (state form)
 *
 * Whitepaper refs
 * - Definition 16 (SafeToSkip inequality): `alpenglow-whitepaper.md:571`.
 * - Safety intuition: once skip(s) + Σ notar(b) − max notar(b) ≥ 40%, the
 *   remaining stake that could still coalesce on any single block is < 80%.
 *
 * Explanation
 * - State-level strengthening: whenever the SafeToSkip guard’s inequality
 *   holds (ignoring the local alreadyVoted/~votedSkip gate), no block of that
 *   slot has ≥80% NotarVote stake in the same Pool. This captures the
 *   paper’s “cannot fast-finalize later” as a safety check usable as an
 *   invariant.
 ***************************************************************************)
SafeToSkipPrecludesFastNow ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        CanEmitSafeToSkip(validators[v].pool, s, TRUE, FALSE)
            => (\A b \in {x \in blocks : x.slot = s} :
                    ~MeetsThreshold(NotarStake(validators[v].pool, s, b.hash), 80))

(***************************************************************************
 * CHAIN CONSISTENCY — restating Theorem 1 under Assumption 1
 *
 * Whitepaper refs
 * - Assumption 1 (<20% byzantine): `alpenglow-whitepaper.md:107`.
 ***************************************************************************)
ChainConsistency == SafetyInvariant

(***************************************************************************
 * LEMMA 20 — vote uniqueness (one initial vote per slot)
 *
 * Whitepaper refs
 * - Lemma 20 (notarization or skip): `alpenglow-whitepaper.md:820`.
 ***************************************************************************)
VoteUniqueness ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET votes == GetVotesForSlot(validators[v].pool, slot)
            initVotes == {vt \in votes : 
                         IsInitialVote(vt) /\ vt.validator = v}
        IN Cardinality(initVotes) <= 1

(***************************************************************************
 * LEMMA 24 — unique notarization per slot
 *
 * Whitepaper refs
 * - Lemma 24 statement: `alpenglow-whitepaper.md:855`.
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
 * GLOBAL NOTARIZATION UNIQUENESS — cross-validator consistency
 *
 * Explanation
 * - Across validators, notarization and notar-fallback certificates agree on
 *   a single block hash per slot.
 ***************************************************************************)
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
 * LEMMA 25 — finalized implies notarized
 *
 * Explanation
 * - Every finalized block must have been covered by a notarization (or fast
 *   finalization) certificate per Def.14.
 ***************************************************************************)
FinalizedImpliesNotarized ==
    \A v \in CorrectNodes :
    \A b \in finalized[v] :
        LET pool == validators[v].pool
        IN \E cert \in pool.certificates[b.slot] :
            /\ cert.type \in {"NotarizationCert", "FastFinalizationCert"}
            /\ cert.blockHash = b.hash

(***************************************************************************
 * CERTIFICATE NON-EQUIVOCATION — no two different certs of same type/slot
 *
 * Whitepaper refs
 * - Definition 13 (certificate generation/storage): `alpenglow-whitepaper.md:520`.
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
 * SKIP VS BLOCK-CERT EXCLUSION — mutual exclusion per slot
 *
 * Explanation
 * - No validator's pool may contain both a SkipCert and any block-related
 *   certificate (Notarization/NotarFallback/FastFinalization) in the same slot.
 * - Mirrors whitepaper arguments that these conditions are mutually exclusive
 *   under the model assumptions; surfaces modeling errors early.
 ***************************************************************************)
PoolSkipVsBlockExclusion ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        SkipVsBlockCertExclusion(validators[v].pool.certificates[s])

(***************************************************************************
 * HONEST NON-EQUIVOCATION — at most one (leader,slot) block if leader correct
 *
 * Explanation
 * - A correct leader does not equivocate within a slot; the model enforces at
 *   most one block per (leader,slot) among correct leaders.
 ***************************************************************************)
HonestNonEquivocation ==
    \A l \in CorrectNodes :
    \A s \in 1..MaxSlot :
        LET bs == {b \in blocks : b.leader = l /\ b.slot = s}
        IN Cardinality(bs) <= 1

(***************************************************************************
 * TRANSIT CERTIFICATES VALID — in-flight certificates are well-formed
 *
 * Whitepaper refs
 * - Messages and certificates types (Tables 5–6): see §2.4 around `alpenglow-whitepaper.md:474`–`:520`.
 ***************************************************************************)
TransitCertificatesValid ==
    \A c \in messages : c \in Certificate => IsValidCertificate(c)

(***************************************************************************
 * LOCAL VOTES WELL-FORMED — correct nodes' own votes are valid and
 * match their recorded slot. This captures the intended well-formedness
 * of locally created votes and guards against slot–hash pairing mistakes
 * at call sites (mitigated further by CreateNotarVoteForBlock).
 ***************************************************************************)
LocalVotesWellFormed ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        \A vt \in validators[v].pool.votes[s][v] :
            IsValidVote(vt) /\ vt.slot = s

(***************************************************************************
 * FAST ⇒ NOTAR (subset) — Pool-level implication per Table 6
 *
 * Whitepaper refs
 * - "fast ⇒ notar ⇒ fallback" implication: `alpenglow-whitepaper.md:534` • §2.5.
 *
 * Explanation
 * - For every slot’s certificate set in each correct validator’s pool,
 *   if a fast-finalization certificate exists, a matching notarization
 *   certificate also exists with a vote set that is a subset of the fast one.
 *************************************************************************)
PoolFastPathImplication ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        FastPathImplication(validators[v].pool.certificates[s])

(***************************************************************************
 * FINALIZATION ⇒ NOTARIZATION (slot presence) — Def. 14 pairing
 *
 * Explanation
 * - For each validator's Pool and each slot, the presence of a
 *   FinalizationCert implies the presence of some NotarizationCert in the
 *   same slot set. This captures the Def.14 pairing at the storage level.
 *************************************************************************)
PoolFinalizationImpliesNotarizationPresent ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        FinalizationImpliesNotarizationPresent(validators[v].pool, s)

(***************************************************************************
 * CERT BLOCK PROVENANCE — stored block-bearing certs reference known blocks
 *
 * Explanation
 * - Any stored certificate that carries a block hash must reference the
 *   hash of some block present in `blocks`. This documents the modeling
 *   assumption that certificates are only formed for extant blocks.
 *************************************************************************)
CertificateBlockProvenance ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        \A c \in validators[v].pool.certificates[s] :
            (c.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}) =>
            c.blockHash \in {b.hash : b \in blocks}

\* Pool storage guarantees from Definitions 12–13 (whitepaper §2.5)
PoolMultiplicityOK ==
    \A v \in Validators : MultiplicityRulesRespected(validators[v].pool)

PoolCertificateUniqueness ==
    \A v \in Validators : CertificateUniqueness(validators[v].pool)

\* All stored certificates are valid (Tables 5–6; Pool §2.5)
PoolCertificatesValid ==
    \A v \in Validators :
    \A s \in 1..MaxSlot :
        AllCertificatesValid(validators[v].pool.certificates[s])

\* All stored certificates are structurally well-formed (Vote relevance)
PoolCertificatesWellFormedOK ==
    \A v \in Validators : CertificatesWellFormed(validators[v].pool)

\* Pool alignment invariants (audit 0009): slot/validator alignment for votes,
\* and slot alignment for certificates across all validators.
PoolAlignmentOK ==
    \A v \in Validators :
        /\ PoolVotesSlotValidatorAligned(validators[v].pool)
        /\ PoolCertificatesSlotAligned(validators[v].pool)

\* Bucket–slot consistency (audit 0013): explicit alias assertion
BucketSlotConsistencyOK ==
    \A v \in Validators : BucketSlotConsistency(validators[v].pool)

\* Optional sanity (audit 0010): TotalNotarStake equals the stake of
\* unique notar voters per slot in each validator's pool.
TotalNotarStakeSanity ==
    \A v \in Validators :
    \A s \in 1..MaxSlot :
        TotalNotarStakeEqualsUniqueNotarVoters(validators[v].pool, s)

(*
 * TIMEOUTS IN FUTURE — never schedule a timeout in the past
 *
 * Whitepaper refs
 * - Definition 17 guarantees (i − s + 1) ≥ 1 for ParentReady on first slot:
 *   `alpenglow-whitepaper.md:613` • p.23.
 *)
TimeoutsInFuture ==
    \A v \in CorrectNodes:
        \A s \in 1..MaxSlot:
            LET timeout == validators[v].timeouts[s]
            IN timeout = 0 \/ timeout > validators[v].clock

(***************************************************************************
 * ROTOR SELECTION SOUNDNESS — structural constraints when successful
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
 * BASIC LIVENESS — after GST, something new finalizes eventually
 ***************************************************************************)
BasicLiveness ==
    (time >= GST) ~> 
        (\E v \in Validators :
             \E b \in blocks : b.slot > 0 /\ b \in finalized[v])

(***************************************************************************
 * PROGRESS — highest finalized slot keeps increasing after GST
 ***************************************************************************)
Progress ==
    (time >= GST) ~>
        (\A v \in Validators :
             LET currentMax == IF finalized[v] = {} THEN 0
                                 ELSE CHOOSE s \in {b.slot : b \in finalized[v]} :
                                          \A s2 \in {b.slot : b \in finalized[v]} : s >= s2
             IN <>(\E b \in blocks : b.slot > currentMax /\ b \in finalized[v]))

(***************************************************************************
 * THEOREM 2 — window-level liveness (Section 2.10)
 *
 * Whitepaper refs
 * - Theorem 2 statement: `alpenglow-whitepaper.md:1045`.
 * - No pre-GST timeouts premise: captured via NoTimeoutsBeforeGST; see §2.10.
 ***************************************************************************)
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
 * Commentary: Under the stated premises (correct window leader, no pre-GST
 * timeouts, and post-GST delivery/fairness), every slot in the leader’s
 * window is eventually finalized by all correct nodes (Thm. 2).
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
 * IMPLIED: ParentReady implies requisite certificates exist
 *
 * Whitepaper refs
 * - Definition 15 (ParentReady preconditions): `alpenglow-whitepaper.md:543`–`:546`.
 ***************************************************************************)
ParentReadyImpliesCert ==
    \A v \in CorrectNodes, s \in 1..MaxSlot:
        (s > 1 /\ "ParentReady" \in validators[v].state[s]) =>
            \E p \in blocks:
                ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)

(***************************************************************************
 * IMPLIED: ParentReady uses a previous block (model assurance)
 *
 * Audit mapping
 * - Definition 15 says "previous block b"; make it explicit that the block
 *   witnessing ParentReady for slot s must satisfy p.slot < s.
 ***************************************************************************)
ParentReadyUsesPreviousBlock ==
    \A v \in CorrectNodes, s \in 1..MaxSlot:
        (s > 1 /\ "ParentReady" \in validators[v].state[s]) =>
            \E p \in blocks :
                /\ p.slot < s
                /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)

(***************************************************************************
 * IMPLIED: BlockNotarized implies notarization certificate exists
 *
 * Whitepaper refs
 * - Definition 15 (BlockNotarized event): `alpenglow-whitepaper.md:543`.
 ***************************************************************************)
BlockNotarizedImpliesCert ==
    \A v \in CorrectNodes, s \in 1..MaxSlot :
        (\E b \in blocks : b.slot = s /\ "BlockNotarized" \in validators[v].state[s]) =>
        (\E b \in blocks : b.slot = s /\ HasNotarizationCert(validators[v].pool, s, b.hash))

(* --------------------------------------------------------------------------
 * IMPLIED: FinalVote implies BlockNotarized for that slot (cross-module aid)
 *
 * Audit suggestion: make explicit that a correct node only issues/stores a
 * FinalVote(s) after observing BlockNotarized(s) locally. TryFinal enforces
 * this guard; the invariant documents it for model checking.
 * -------------------------------------------------------------------------- *)
FinalVoteImpliesBlockNotarized ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        \A vt \in validators[v].pool.votes[s][v] :
            IsFinalVote(vt) => HasState(validators[v], s, "BlockNotarized")

(* --------------------------------------------------------------------------
 * FINALIZED ANCESTOR CLOSURE — finalized sets are ancestry-closed
 *
 * If a validator has finalized b, then all ancestors of b (w.r.t. global
 * blocks) are also finalized by that validator. This documents and checks the
 * closure property relied upon by SingleChain over finalized sets.
 * -------------------------------------------------------------------------- *)
FinalizedAncestorClosure ==
    \A v \in Validators : \A b \in finalized[v] :
        GetAncestors(b, blocks) \subseteq finalized[v]

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


\* ============================================================================
\* MAIN INVARIANT (Combines all safety properties)
\* ============================================================================

Invariant ==
    /\ TypeInvariant
    /\ SafetyInvariant
    /\ NoConflictingFinalization
    /\ SafeToSkipPrecludesFastNow
    /\ ChainConsistency
    /\ VoteUniqueness
    /\ UniqueNotarization
    /\ GlobalNotarizationUniqueness
    /\ FinalizedImpliesNotarized
    /\ CertificateNonEquivocation
    /\ PoolSkipVsBlockExclusion
    /\ HonestNonEquivocation
    /\ TransitCertificatesValid
    /\ LocalVotesWellFormed
    /\ PoolFastPathImplication
    /\ PoolFinalizationImpliesNotarizationPresent
    /\ CertificateBlockProvenance
    /\ ByzantineStakeOK
    /\ PoolMultiplicityOK
    /\ PoolCertificateUniqueness
    /\ PoolCertificatesValid
    /\ PoolCertificatesWellFormedOK
    /\ PoolAlignmentOK
    /\ BucketSlotConsistencyOK
    /\ RotorSelectSoundness
    /\ TimeoutsInFuture
    /\ UniqueBlockHashes(blocks)
    /\ FinalizedAncestorClosure
    /\ BlockNotarizedImpliesCert
    /\ ParentReadyImpliesCert
    /\ ParentReadyUsesPreviousBlock
    /\ FinalVoteImpliesBlockNotarized
    /\ TotalNotarStakeSanity

=============================================================================
