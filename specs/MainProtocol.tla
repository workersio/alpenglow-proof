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
    MaxBlocks,          \* Maximum blocks for bounded model checking
    \* Bounded-time finalization latency parameters (whitepaper §1.3, §1.5, §2.6)
    Delta80,            \* Models δ80% (time unit consistent with `time`)
    Delta60             \* Models δ60% (time unit consistent with `time`)

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
    /\ Slots = 1..MaxSlot   \* Protocol slots s ≥ 1 (whitepaper §1.5 p. 213); genesis is slot 0
    /\ Delta80 \in Nat \ {0}
    /\ Delta60 \in Nat \ {0}

\* ============================================================================
\* SYSTEM STATE VARIABLES
\* ============================================================================

VARIABLES
    validators,         \* Map: Validators -> ValidatorState
    blocks,             \* Set of all blocks in the system
    messages,           \* Set of messages in transit
    byzantineNodes,     \* Set of Byzantine validator IDs
    unresponsiveNodes,  \* Set of honest-but-unresponsive validator IDs
    time,               \* Global time (for modeling synchrony)
    finalized,          \* Map: Validators -> Set of finalized blocks
    blockAvailability,  \* Map: Validators -> Set of reconstructed blocks
    \* Ghost timers to enforce bounded-time finalization (min(δ80%, 2δ60%)).
    \* They record the first model time at which a block (slot s, hash h)
    \* becomes available to ≥80% or ≥60% of stake, respectively.
    avail80Start,       \* [1..MaxSlot -> [BlockHashes -> Nat]]; 0 means “not started”
    avail60Start        \* [1..MaxSlot -> [BlockHashes -> Nat]]; 0 means “not started”

vars == <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

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

\* Get correct, responsive validators (non-Byzantine and not unresponsive)
CorrectNodes == Validators \ (byzantineNodes \cup unresponsiveNodes)

\* Stake premises (Assumptions 1 and 2)
ByzantineStakeOK == (CalculateStake(byzantineNodes) * 100) < (TotalStake * 20)
UnresponsiveStakeOK ==
    /\ (CalculateStake(unresponsiveNodes) * 100) <= (TotalStake * 20)
    /\ (byzantineNodes \cap unresponsiveNodes) = {}

(***************************************************************************
 * ASSUMPTION 2 — extended crash tolerance (§1.2)
 *
 * Whitepaper refs
 * - Assumption 2 statement: `alpenglow-whitepaper.md:122`.
 *
 * Explanation
 * - Byzantine nodes < 20% stake (Assumption 1, also enforced separately)
 * - Unresponsive/crashed nodes ≤ 20% stake (additional tolerance)
 * - Byzantine and unresponsive sets are disjoint
 * - Correct (responsive) nodes > 60% stake (derived from above)
 * - This predicate explicitly groups all Assumption 2 requirements for
 *   auditability and use in liveness properties (issues_claude.md §15).
 ***************************************************************************)
Assumption2OK ==
    /\ ByzantineStakeOK
    /\ UnresponsiveStakeOK
    /\ (CalculateStake(CorrectNodes) * 100) > (TotalStake * 60)

\* Repair trigger (Algorithm 4; §2.8). Include fast-finalization to cover fast-only
\* implementations. See also Blokstor repair mention: `alpenglow-whitepaper.md:470`.
\* Note: Genesis (slot 0) never needs repair - it's available to all nodes at Init.
NeedsBlockRepair(pool, block) ==
    LET slot == block.slot
        hash == block.hash
    IN /\ slot \in Slots  \* Only protocol slots; genesis is outside pool domain
       /\ (HasFastFinalizationCert(pool, slot, hash)
           \/ HasNotarizationCert(pool, slot, hash)
           \/ HasNotarFallbackCert(pool, slot, hash))

\* Check if we're after GST (network is stable; §1.5/§2.10)
AfterGST == time >= GST

\* Assumption 1: Byzantine stake < 20% of total (`alpenglow-whitepaper.md:107`)
\* (used inline in Init/Invariant/Liveness properties)
\* Honest participation bound: at most 20% unresponsive stake (used inline)

\* ============================================================================
\* AVAILABILITY-STAKE HELPERS (for bounded-time finalization)
\* ============================================================================

(***************************************************************************
 * AvailabilityStakeFor(s, h): stake of validators that currently have block
 * (slot s, hash h) in their `blockAvailability`. This abstracts the
 * whitepaper's δ_θ notion (Section 1.5 at :241) by detecting when a block
 * has reached ≥θ% stake of nodes.
 * 
 * DESIGN CHOICE: We measure availability only over CorrectNodes (honest + 
 * responsive), excluding Byzantine and crashed nodes. The whitepaper's δ_θ
 * definition doesn't explicitly specify the domain, stating only "a set of 
 * nodes with cumulative stake at least θ". We interpret this as correct 
 * nodes because:
 * - Byzantine nodes can arbitrarily delay/refuse participation
 * - Crashed nodes by definition cannot participate in message exchange
 * - δ_θ timing guarantees only make sense for cooperating nodes
 * This interpretation ensures sound bounded-time finalization analysis.
 ***************************************************************************)
ExistsBlockAt(s, h) == \E b \in blocks : b.slot = s /\ b.hash = h

AvailabilityStakeFor(s, h) ==
    LET holders == { v \in CorrectNodes :
                        \E b \in blockAvailability[v] : b.slot = s /\ b.hash = h }
    IN CalculateStake(holders)

AvailMeets(s, h, thetaPercent) ==
    MeetsThreshold(AvailabilityStakeFor(s, h), thetaPercent)

Avail80Now(s, h) == AvailMeets(s, h, 80)
Avail60Now(s, h) == AvailMeets(s, h, 60)

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
    /\ unresponsiveNodes \in SUBSET (Validators \ byzantineNodes)
    /\ (CalculateStake(byzantineNodes) * 100) < (TotalStake * 20)
    /\ (CalculateStake(unresponsiveNodes) * 100) <= (TotalStake * 20)
    /\ time = 0
    /\ finalized = [v \in Validators |-> {}]
    /\ blockAvailability = [v \in Validators |-> {GenesisBlock}]
    /\ avail80Start = [s \in 1..MaxSlot |-> [h \in BlockHashes |-> 0]]
    /\ avail60Start = [s \in 1..MaxSlot |-> [h \in BlockHashes |-> 0]]

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
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

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
             IN /\ messages' = messages \cup {cert}
                /\ validators' = [validators EXCEPT ![v].pool = StoreCertificate(validators[v].pool, cert)]
    /\ UNCHANGED <<blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

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
    /\ block.slot \in Slots  \* Only protocol blocks; genesis is pre-finalized at Init
    /\ LET pool == validators[v].pool
           slot == block.slot
       IN \/ HasFastFinalizationCert(pool, slot, block.hash)
          \/ CanFinalizeSlow(pool, slot, block.hash)
    /\ finalized' = [finalized EXCEPT ![v] = finalized[v] \cup GetAncestors(block, blocks)]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, blockAvailability, avail80Start, avail60Start>>

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
        /\ messages' = messages \cup {vote}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

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
          /\ blocks' = blocks \cup {newBlock}
          /\ blockAvailability' = [blockAvailability EXCEPT ![leader] = @ \cup {newBlock}]
          /\ UNCHANGED <<validators, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>

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
          /\ blocks' = blocks \cup {newBlock}
          /\ \E recipients \in SUBSET Validators :
                blockAvailability' =
                    [w \in Validators |->
                        IF w \in recipients THEN blockAvailability[w] \cup {newBlock}
                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>

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
    /\ avail80Start' =
        [s \in 1..MaxSlot |->
            [h \in BlockHashes |->
                IF avail80Start[s][h] # 0 THEN avail80Start[s][h]
                ELSE IF ExistsBlockAt(s, h) /\ Avail80Now(s, h)
                     THEN time'
                     ELSE 0
            ]
        ]
    /\ avail60Start' =
        [s \in 1..MaxSlot |->
            [h \in BlockHashes |->
                IF avail60Start[s][h] # 0 THEN avail60Start[s][h]
                ELSE IF ExistsBlockAt(s, h) /\ Avail60Now(s, h)
                     THEN time'
                     ELSE 0
            ]
        ]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, finalized, blockAvailability>>

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
       IN /\ needers # {}
          /\ \E bins \in BinCandidates(needers, nextLeader) :
                /\ RotorSuccessfulBins(block.leader, bins, CorrectNodes)
                /\ LET relays == BinsToRelaySet(bins)
                   IN /\ relays # {}
                      /\ blockAvailability' =
                            [w \in Validators |->
                                IF w \in CorrectNodes
                                THEN blockAvailability[w] \cup {block}
                                ELSE blockAvailability[w]]
                      /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>

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
       IN /\ needers # {}
          /\ \E bins \in BinCandidates(needers, nextLeader) :
                /\ ~RotorSuccessfulBins(block.leader, bins, CorrectNodes)
                /\ LET relays == BinsToRelaySet(bins)
                   IN /\ relays # {}
                      /\ blockAvailability' = [w \in Validators |->
                                                IF w \in relays
                                                THEN blockAvailability[w] \cup {block}
                                                ELSE blockAvailability[w]]
                      /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>

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
                                        THEN blockAvailability[w] \cup {block}
                                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>

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
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>


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
    /\ blockAvailability' = [blockAvailability EXCEPT ![v] = @ \cup {block}]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized, avail80Start, avail60Start>>


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
    /\ UNCHANGED <<blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

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
    /\ UNCHANGED <<blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

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
          /\ messages' = messages \cup {vt}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

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
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>> \* Finalization votes broadcasted by BroadcastLocalVote

 (***************************************************************************
 * EVENT: SAFE TO NOTAR — fallback inequality (Definition 16)
 *
 * Whitepaper refs
 * - Definition 16 (SafeToNotar): `alpenglow-whitepaper.md:554`–`:556` • p.21–22.
 *   • Formula (page 22): notar(b) ≥ 40% OR (skip(s)+notar(b) ≥ 60% AND notar(b) ≥ 20%).
 *
 * Explanation
 * - When that inequality holds and the node hasn't already voted to notarize b
 *   in slot s, emit the event and cast notar-fallback accordingly (Alg.1).
 * - We pass the full block `b` into the handler and use the typed wrapper
 *   to ensure slot–hash pairing by construction; creation occurs only under
 *   the CanEmitSafeToNotar guard above (aid to model checking).
 *
 * AUDIT NOTE (issues_claude.md §3):
 * Re-emission suppression: The guard `~HasState(validator, s, "BadWindow")`
 * prevents emitting SafeToNotar multiple times per slot. Algorithm 1 (:656-:660)
 * checks `ItsOver ∉ state[s]` and sets `BadWindow` after emission, ensuring
 * at-most-once semantics through atomicity. The spec's BadWindow check is a
 * sound strengthening that makes the at-most-once property explicit: once any
 * fallback vote is cast (setting BadWindow), no further SafeToNotar/SafeToSkip
 * events are emitted for that slot. This prevents redundant event processing
 * and aligns with the whitepaper's intent that fallback paths are terminal for
 * the slot's voting lifecycle.
 ***************************************************************************)
EmitSafeToNotar ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, b \in blocks :
         /\ b.slot = s
         /\ b \in blockAvailability[v]
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedForB == VotedForBlock(validators[v], s, b.hash)
            IN CanEmitSafeToNotar(validators[v].pool, s, b.hash, b.slot - 1, b.parent, alreadyVoted, votedForB)
         /\ ~HasState(validators[v], s, "BadWindow") \* Prevents re-emitting after a fallback vote was cast (see audit note above)
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToNotar(@, b)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

 (***************************************************************************
 * EVENT: SAFE TO SKIP — fallback inequality (Definition 16)
 *
 * Whitepaper refs
 * - Definition 16 (SafeToSkip): `alpenglow-whitepaper.md:571` • p.22.
 *   • Formula (page 22): skip(s) + Σ notar(b) − max_b notar(b) ≥ 40%.
 *
 * Explanation
 * - When that inequality holds and the node hasn't already voted to skip s,
 *   emit SafeToSkip(s) and cast a skip-fallback vote (Alg.1).
 *
 * AUDIT NOTE (issues_claude.md §3):
 * Re-emission suppression: The guard `~HasState(validator, s, "BadWindow")`
 * prevents emitting SafeToSkip multiple times per slot. Algorithm 1 (:662-:666)
 * checks `ItsOver ∉ state[s]` and sets `BadWindow` after emission. The spec's
 * BadWindow check makes the at-most-once property explicit and aligns with the
 * whitepaper's intent that fallback events mark the slot as terminal for normal
 * voting. See parallel reasoning in EmitSafeToNotar audit note above.
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
         /\ ~HasState(validators[v], s, "BadWindow") \* Prevents re-emitting after a fallback vote was cast (see audit note above)
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToSkip(@, s)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

 (***************************************************************************
 * EVENT: PARENT READY — first slot of a leader window (Definition 15)
 *
 * Whitepaper refs
 * - Definition 15 (ParentReady): `alpenglow-whitepaper.md:543`–`:546` • p.21.
 *
 * Explanation
 * - Mark the first slot of a new leader window once predecessors are certified.
 * - First-slot guard enforced by ShouldEmitParentReady (uses IsFirstSlotOfWindow).
 ***************************************************************************)
EmitParentReady ==
    \* Note: The model assumes certificates refer to p \in blocks (consistent with 
    \* how votes and certs are created), clarifying why p is quantified from blocks.
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, p \in blocks :
         /\ p.slot < s  \* Only consider previous blocks as parents (Def. 15)
         /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)
         /\ ~HasState(validators[v], s, "ParentReady")
         /\ validators' = [validators EXCEPT ![v] = HandleParentReady(@, s, p.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

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
    \* Proposer uses the strict ParentReady‑gated variant (Alg. 3).
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
        b.slot \in Slots =>  \* Only protocol blocks have certificates; genesis excluded
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
 * LEMMA 21 — fast-finalization property (§2.9)
 *
 * Whitepaper refs
 * - Lemma 21 statement: `alpenglow-whitepaper.md:824`.
 *
 * Explanation
 * - If a block b is fast-finalized (≥80% NotarVote), then in the same slot:
 *   (i) no other block b' can be notarized
 *   (ii) no other block b' can be notarized-fallback
 *   (iii) there cannot exist a skip certificate
 * - This is subsumed by SafetyInvariant and NoConflictingFinalization but
 *   stated explicitly per audit recommendation (issues_claude.md §14).
 ***************************************************************************)
Lemma21_FastFinalizationProperty ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        LET pool == validators[v].pool
            fastCerts == {c \in pool.certificates[s] : c.type = "FastFinalizationCert"}
        IN \A fc \in fastCerts :
            LET h == fc.blockHash
                otherNotarCerts == {c \in pool.certificates[s] :
                    /\ c.type \in {"NotarizationCert", "NotarFallbackCert"}
                    /\ c.blockHash # h}
                skipCerts == {c \in pool.certificates[s] : c.type = "SkipCert"}
            IN /\ otherNotarCerts = {}  \* (i) and (ii)
               /\ skipCerts = {}        \* (iii)

(***************************************************************************
 * LEMMA 22 — no mixing finalization with fallback in the same slot
 *
 * Explanation
 * - Validator-local mutual exclusion: ItsOver and BadWindow never co-exist
 *   in a slot. Encoded via VotorCore's per-validator predicates.
 *************************************************************************)
NoMixFinalizationAndFallback ==
    \A v \in CorrectNodes :
        Lemma22_ItsOverImpliesNotBadWindow(validators[v]) /\
        Lemma22_BadWindowImpliesNotItsOver(validators[v])

(***************************************************************************
 * LEMMA 23 — > 40% correct stake prevents conflicting notarizations
 *
 * Whitepaper refs
 * - Lemma 23 statement: `alpenglow-whitepaper.md:851`.
 *
 * Explanation
 * - If correct nodes with >40% stake cast notarization votes for block b in
 *   slot s, no other block can be notarized in slot s.
 * - This is subsumed by UniqueNotarization and vote uniqueness (Lemma 20),
 *   but stated explicitly per audit recommendation (issues_claude.md §14).
 ***************************************************************************)
Lemma23_FortyPercentPreventsConflictingNotar ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        LET pool == validators[v].pool
            \* For each block hash h with notar votes from correct nodes
            notarVotesForHash(h) == {vote \in GetVotesForSlot(pool, s) :
                /\ IsInitialNotarVote(vote)
                /\ vote.blockHash = h
                /\ vote.validator \in CorrectNodes}
            \* Check: if any hash h has >40% correct stake, no other hash has ≥60%
            hashesWithOver40 == {h \in BlockHashes :
                MeetsThreshold(StakeFromVotes(notarVotesForHash(h)), 41)}
        IN \A h1, h2 \in hashesWithOver40 : h1 = h2  \* At most one hash has >40%

(***************************************************************************
 * LEMMA 26 — slow-finalization property (§2.9)
 *
 * Whitepaper refs
 * - Lemma 26 statement: `alpenglow-whitepaper.md:872`.
 *
 * Explanation
 * - If a block b is slow-finalized (≥60% FinalVote + notarization), then:
 *   (i) no other block b' can be notarized
 *   (ii) no other block b' can be notarized-fallback
 *   (iii) there cannot exist a skip certificate
 * - This is subsumed by SafetyInvariant and FinalizedImpliesNotarized but
 *   stated explicitly per audit recommendation (issues_claude.md §14).
 ***************************************************************************)
Lemma26_SlowFinalizationProperty ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        LET pool == validators[v].pool
            finalizationCerts == {c \in pool.certificates[s] : c.type = "FinalizationCert"}
        IN \A fc \in finalizationCerts :
            \* Finalization cert implies unique notarized block (Lemma 24+25)
            LET notarCerts == {c \in pool.certificates[s] : c.type = "NotarizationCert"}
            IN notarCerts # {} =>
                LET h == (CHOOSE c \in notarCerts : TRUE).blockHash
                    otherNotarCerts == {c \in pool.certificates[s] :
                        /\ c.type \in {"NotarizationCert", "NotarFallbackCert"}
                        /\ c.blockHash # h}
                    skipCerts == {c \in pool.certificates[s] : c.type = "SkipCert"}
                IN /\ Cardinality(notarCerts) = 1  \* Unique notarization (Lemma 24)
                   /\ otherNotarCerts = {}         \* (i) and (ii)
                   /\ skipCerts = {}               \* (iii)

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
 * TRANSIT VOTES VALID in-flight votes are well-formed
 *
 * Audit suggestion (messages well-typed): ensure every vote present in the
 * network set `messages` satisfies IsValidVote. Complements
 * TransitCertificatesValid for certificates.
 *************************************************************************)
 
TransitVotesValid ==
    \A v \in messages : v \in Vote => IsValidVote(v)

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
 * FAST ⇒ NOTAR (threshold) — Pool-level implication per Table 6
 *
 * Whitepaper refs
 * - "fast ⇒ notar ⇒ fallback" implication: `alpenglow-whitepaper.md:534` • §2.5.
 *
 * Explanation
 * - For every slot’s certificate set in each correct validator’s pool,
 *   if a fast-finalization certificate exists, a matching notarization
 *   certificate also exists for the same (slot, blockHash).
 * - This uses the threshold-only relation (existence) to align with the
 *   whitepaper and avoid over-constraining network-learned certificates.
 * - A stricter subset-based variant remains available as
 *   `FastPathImplication` in Certificates.tla for stronger checks if desired.
 *************************************************************************)
PoolFastPathImplication ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        FastImpliesNotarThresholdOnly(validators[v].pool.certificates[s])

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

\* Optional strengthening (audit suggestion): for correct nodes, all stored
\* NotarFallbackVote(s) by that node in a given slot agree on the same block.
PoolNotarFallbackBlockConsistencyOK ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        NotarFallbackBlockConsistencyAt(validators[v].pool, s, v)

\* Optional sequencing check (audit suggestion): for correct nodes, the
\* presence of a SkipFallbackVote(s) implies an initial NotarVote(s) exists
\* in the same node’s Pool for that slot.
PoolSkipFallbackAfterInitialNotarOK ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        SkipFallbackAfterInitialNotarAt(validators[v].pool, s, v)

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

\* Local clock monotonicity (audit 0017): correct nodes' local clocks never
\* move ahead of the model time and, combined with AdvanceTime, are
\* non-decreasing across steps.
LocalClockMonotonic ==
    \A v \in CorrectNodes : validators[v].clock <= time

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
\* Liveness property (enabled in MC.cfg PROPERTIES)
BasicLiveness ==
    (time >= GST) ~> 
        (\E v \in Validators :
             \E b \in blocks : b.slot > 0 /\ b \in finalized[v])

(***************************************************************************
 * FAST PATH (ONE ROUND) — >=80% responsive stake implies fast finalization
 *
 * Whitepaper refs
 * - Sections 1.3 and 2.6: one-round finalization with >=80% participating
 *   stake; Tables 5–6 thresholds (NotarVote 80% => FastFinalizationCert).
 *
 * Explanation
 * - Once a FastFinalizationCert exists for a block b in slot s (i.e., >=80%
 *   stake on NotarVote for b), the protocol can finalize b in that same
 *   round without a slow-path FinalizationCert. Under post-GST fairness,
 *   some correct node will eventually execute FinalizeBlock on b.
 *
 * Notes
 * - We quantify over blocks present in the model state and restrict to
 *   production slots (1..MaxSlot). The antecedent uses presence of a fast
 *   certificate in any correct node’s Pool, which captures the 
 *   ">=80% responsive stake" condition operationally.
 ***************************************************************************)

\* Liveness property (enabled in MC.cfg PROPERTIES)
FastCertExistsAt(s, h) ==
    \E v \in CorrectNodes : HasFastFinalizationCert(validators[v].pool, s, h)

BlockHashFinalizedAt(s, h) ==
    \E v \in CorrectNodes : \E b \in blocks : b.slot = s /\ b.hash = h /\ b \in finalized[v]

FastPathOneRound ==
    \A s \in 1..MaxSlot :
    \A h \in BlockHashes :
        ((time >= GST /\ FastCertExistsAt(s, h)) ~>
            BlockHashFinalizedAt(s, h))

(***************************************************************************
 * TRYFINAL PROGRESS — BlockNotarized + local vote ⇒ FinalVote eventually
 *
 * Audit 0016 suggestion
 * - If a correct node has observed BlockNotarized(s, h) and later also has a
 *   local NotarVote for the same h in slot s, and the slot is not marked
 *   BadWindow, then it eventually issues/stores FinalVote(s) in its Pool.
 *
 * Explanation
 * - This captures the model’s expectation that once TryFinal’s guard holds
 *   (BlockNotarized ∧ VotedForBlock ∧ ¬BadWindow), weak fairness on the
 *   scheduling of event emissions and handlers leads to FinalVote(s).
 *************************************************************************)
\* Liveness helper (enabled in MC.cfg PROPERTIES)
TryFinalProgress ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ( /\ HasState(validators[v], s, "BlockNotarized")
          /\ ~HasState(validators[v], s, "BadWindow")
          /\ (\E h \in BlockNotarizedHashes(validators[v], s) :
                  VotedForBlock(validators[v], s, h))
        ) ~>
        (<> (\E vt \in validators[v].pool.votes[s][v] : IsFinalVote(vt)))

(***************************************************************************
 * PROGRESS — highest finalized slot keeps increasing after GST
 ***************************************************************************)
\* Liveness property (enabled in MC.cfg PROPERTIES)
Progress ==
    (time >= GST) ~>
        (\A v \in Validators :
            IF v \in CorrectNodes
            THEN LET currentMax == IF finalized[v] = {} THEN 0
                                   ELSE CHOOSE s \in {b.slot : b \in finalized[v]} :
                                            \A s2 \in {b.slot : b \in finalized[v]} : s >= s2
                 IN <>(\E b \in blocks : b.slot > currentMax /\ b \in finalized[v])
            ELSE TRUE)

(***************************************************************************
 * SLOW-PATH LIVENESS (≥60% responsive) — progress after GST
 *
 * Explanation
 * - Under the stake premises encoded by ByzantineStakeOK and UnresponsiveStakeOK,
 *   at least 60% of stake is responsive and honest. Combined with the fairness
 *   constraints (AfterGST), the protocol makes progress (finalizes higher slots).
 ***************************************************************************)
\* Liveness property (enabled in MC.cfg PROPERTIES)
\* Stake assumptions are enforced in Init/Invariant; see comments above.
Liveness60Responsive == Progress

(***************************************************************************
 * CRASH-TOLERANT LIVENESS (≤20% non-responsive stake)
 *
 * Whitepaper refs
 * - Assumption 2 (extra crash tolerance): alpenglow-whitepaper.md:122 (page 5)
 *   "Byzantine < 20%, up to 20% crashed, remaining > 60% correct."
 * - Liveness under partial synchrony (Thm. 2): alpenglow-whitepaper.md:1045.
 *
 * Explanation
 * - After GST, provided Assumption2OK holds (Byzantine < 20%, unresponsive ≤ 20%,
 *   correct > 60% stake), every correct/responsive validator eventually finalizes
 *   a block with a strictly higher slot than its current maximum (i.e., makes progress).
 * - Assumption2OK is enforced in Invariant, so this property is checked under
 *   the extended crash tolerance model.
 ***************************************************************************)
CrashToleranceLiveness20 ==
    (time >= GST) ~>
        (\A v \in Validators :
            IF v \in CorrectNodes
            THEN LET currentMax == IF finalized[v] = {} THEN 0
                                   ELSE CHOOSE s \in {b.slot : b \in finalized[v]} :
                                            \A s2 \in {b.slot : b \in finalized[v]} : s >= s2
                 IN <>(\E b \in blocks : b.slot > currentMax /\ b \in finalized[v])
            ELSE TRUE)

(***************************************************************************
 * REPAIR LIVENESS — notarized blocks eventually available to all correct nodes
 *
 * Whitepaper refs
 * - Algorithm 4 (Repair): `alpenglow-whitepaper.md:801` • §2.8
 * - Definition 19 (repair functions): `alpenglow-whitepaper.md:782`
 * - Blokstor repair obligation: `:470`
 *
 * Explanation
 * - If a correct node needs a block (has a certificate for it but lacks the block),
 *   then eventually that node will have the block available.
 * - This property verifies the repair mechanism's liveness guarantee: correct
 *   nodes eventually obtain all notarized blocks they need for protocol progress.
 * - Combined with weak fairness on RepairBlock (line 810), this ensures the
 *   repair mechanism fulfills its role in maintaining block availability.
 * 
 * Note: Due to TLC limitations with temporal quantification over variables, we define
 * a helper state predicate and use it in a simpler temporal formula. This checks that
 * any blocks needed for repair eventually become available.
 ***************************************************************************)

\* Helper: Check if any correct node needs repair for a block it doesn't have
NodeNeedsRepair(v) ==
    v \in CorrectNodes /\ 
    \E b \in blocks : NeedsBlockRepair(validators[v].pool, b) /\ b \notin blockAvailability[v]

\* The actual liveness property: if a node needs repair after GST, it eventually gets the blocks
RepairEventuallySucceeds ==
    \A v \in Validators :
        ((time >= GST /\ NodeNeedsRepair(v)) ~> 
            ~NodeNeedsRepair(v))

(***************************************************************************
 * THEOREM 2 — window-level liveness (Section 2.10)
 *
 * Whitepaper refs
 * - Theorem 2 statement: `alpenglow-whitepaper.md:1045`.
 * - No pre-GST timeouts premise: captured via NoTimeoutsBeforeGST; see §2.10.
 *
 * AUDIT NOTE (issues_openai.md §2):
 * Theorem 2's antecedent includes "Rotor succeeds for all slots in the window."
 * The spec models Rotor success via nondeterministic actions (RotorDisseminateSuccess)
 * with weak fairness (Fairness clause at line ~765), ensuring eventual success
 * for correct leaders after GST. The WindowRotorSuccessful predicate below
 * makes this assumption explicit for clarity and traceability.
 ***************************************************************************)
NoTimeoutsBeforeGST(startSlot) ==
    \A v \in CorrectNodes :
        \A i \in (WindowSlots(startSlot) \cap 1..MaxSlot) :
            validators[v].timeouts[i] = 0 \/ validators[v].timeouts[i] >= GST

\* Helper predicate: Rotor succeeds for all slots in the window (Theorem 2 antecedent)
\* NOTE: This is a model-checking helper. In practice, success is ensured by:
\* 1. Correct leader (Leader(s) \in CorrectNodes)
\* 2. Sufficient relay stake (Lemma 7, κ > 5/3 and Definition 6 conditions)
\* 3. Weak fairness on RotorDisseminateSuccess after GST (Fairness clause)
\* When checking WindowFinalization liveness, TLC's fairness ensures this predicate
\* eventually holds through the RotorDisseminateSuccess action being taken for
\* each slot's block in the window.
WindowRotorSuccessful(startSlot) ==
    \A i \in (WindowSlots(startSlot) \cap 1..MaxSlot) :
        \E b \in blocks :
            /\ b.slot = i
            /\ b.leader = Leader(startSlot)
            /\ (\A v \in CorrectNodes : b \in blockAvailability[v])

WindowFinalizedState(s) ==
    \A v \in CorrectNodes :
        \A i \in (WindowSlots(s) \cap 1..MaxSlot) :
            \E b \in blocks :
                /\ b.slot = i
                /\ b.leader = Leader(s)
                /\ b \in finalized[v]

(*
 * Commentary: Under the stated premises (correct window leader, no pre-GST
 * timeouts, Rotor success for all window slots, and post-GST delivery/fairness),
 * every slot in the leader's window is eventually finalized by all correct nodes
 * (Whitepaper Theorem 2, alpenglow-whitepaper.md:1045).
 *
 * NOTE — Conditional assumptions, not invariants:
 * - Correct leader: Leader(s) \in CorrectNodes
 * - No early timeouts: NoTimeoutsBeforeGST(s)
 * - Rotor success for window: WindowRotorSuccessful(s)
 * - Post-GST fairness: time >= GST gates fairness in this spec
 *
 * These are liveness antecedents (assumptions) and are intentionally not
 * enforced as invariants. WindowRotorSuccessful appears explicitly below for
 * audit clarity; fairness in this spec ensures it eventually holds for correct
 * leaders after GST.
 *)
\* Window-level liveness (quantified form added below)
WindowFinalization(s) ==
    (IsFirstSlotOfWindow(s)
     /\ Leader(s) \in CorrectNodes
     /\ NoTimeoutsBeforeGST(s)
     /\ WindowRotorSuccessful(s)
     /\ time >= GST) ~>
        WindowFinalizedState(s)

\* Quantified window-liveness (for MC.cfg PROPERTIES)
WindowFinalizationAll ==
    \A s \in 1..MaxSlot : WindowFinalization(s)

\* Window liveness properties (if any) are defined in the MC harness.

\* ============================================================================
\* TYPE INVARIANT
\* ============================================================================

TypeInvariant ==
    /\ validators \in [Validators -> ValidatorState]
    /\ blocks \subseteq Block
    /\ messages \subseteq (Vote \cup Certificate)
    /\ byzantineNodes \subseteq Validators
    /\ unresponsiveNodes \subseteq Validators
    /\ time \in Nat
    /\ finalized \in [Validators -> SUBSET blocks]
    /\ blockAvailability \in [Validators -> SUBSET blocks]
    /\ avail80Start \in [1..MaxSlot -> [BlockHashes -> Nat]]
    /\ avail60Start \in [1..MaxSlot -> [BlockHashes -> Nat]]
    /\ \A v \in Validators : ValidatorStateOK(validators[v])
    \* Certificates validity (Table 6) as a baseline type/shape property
    /\ \A v \in Validators : \A s \in 1..MaxSlot :
            AllCertificatesValid(validators[v].pool.certificates[s])

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

(***************************************************************************
 * STATE–POOL WITNESSES — audit 0014 (Votor StateObject)
 *
 * Explanation
 * - Connects Votor state flags to the existence of corresponding local votes
 *   in Pool for correct nodes. These strengthen auditability and document
 *   intended meanings of the flags.
 *************************************************************************)
VotedConsistency ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ("Voted" \in validators[v].state[s])
            => (\E vt \in validators[v].pool.votes[s][v] : IsInitialVote(vt))

VotedNotarTagConsistency ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ("VotedNotarTag" \in validators[v].state[s])
            => (\E vt \in validators[v].pool.votes[s][v] : vt.type = "NotarVote")

BadWindowWitness ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ("BadWindow" \in validators[v].state[s])
            => (\E vt \in validators[v].pool.votes[s][v] :
                    vt.type \in {"SkipVote", "SkipFallbackVote", "NotarFallbackVote"})

ItsOverWitness ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ("ItsOver" \in validators[v].state[s])
            => (\E vt \in validators[v].pool.votes[s][v] : vt.type = "FinalVote")


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

(***************************************************************************
 * REPRESENTATION INVARIANTS — audit 0015 (InitValidatorState)
 *
 * Explanation
 * - Document the split representation for parameterized state objects and
 *   the intended singleton-pending-blocks discipline.
 *************************************************************************)
ParentReadyConsistencyAll ==
    \A v \in Validators : ParentReadyConsistency(validators[v])

PendingBlocksSingletonAll ==
    \A v \in Validators : PendingBlocksSingleton(validators[v])

PendingBlocksSlotAlignedAll ==
    \A v \in Validators : PendingBlocksSlotAligned(validators[v])

(***************************************************************************
 * BOUNDED-TIME FINALIZATION — min(δ80%, 2δ60%) after distribution
 *
 * Whitepaper refs
 * - Section 1.3 (:126) and §1.5 (:241): δ_θ definition and latency intuition.
 * - §2.6: concurrent 80% one-round and 60% two-round finalization paths.
 *
 * Explanation
 * - We record, per (slot,hash), the first model time at which a block has
 *   been disseminated to ≥80% (resp. ≥60%) stake via `avail80Start` and
 *   `avail60Start`. The following invariants assert that by the time the
 *   model time exceeds those start times by Delta80 (resp. 2·Delta60), some
 *   correct node has finalized that block (BlockHashFinalizedAt).
 *
 * Notes
 * - These are safety-style invariants (deadline cannot be exceeded without
 *   finalization) instead of temporal "within k" operators, which allows
 *   TLC to check bounded-time claims with the existing `time` variable.
 ***************************************************************************)

EffectiveStart(start) == IF start = 0 THEN 0 ELSE IF start < GST THEN GST ELSE start

BoundedFinalization80 ==
    \A s \in 1..MaxSlot :
    \A h \in BlockHashes :
        LET st == EffectiveStart(avail80Start[s][h])
        IN (st = 0) \/ (time <= st + Delta80) \/ BlockHashFinalizedAt(s, h)

BoundedFinalization60 ==
    \A s \in 1..MaxSlot :
    \A h \in BlockHashes :
        LET st == EffectiveStart(avail60Start[s][h])
        IN (st = 0) \/ (time <= st + (2 * Delta60)) \/ BlockHashFinalizedAt(s, h)

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
    /\ Lemma21_FastFinalizationProperty
    /\ NoMixFinalizationAndFallback
    /\ Lemma23_FortyPercentPreventsConflictingNotar
    /\ Lemma26_SlowFinalizationProperty
    /\ PoolSkipVsBlockExclusion
    /\ HonestNonEquivocation
    /\ TransitCertificatesValid
    /\ TransitVotesValid
    /\ LocalVotesWellFormed
    /\ PoolFastPathImplication
    /\ PoolFinalizationImpliesNotarizationPresent
    /\ CertificateBlockProvenance
    /\ ByzantineStakeOK
    /\ Assumption2OK
    /\ PoolMultiplicityOK
    /\ PoolCertificateUniqueness
    /\ PoolCertificatesValid
    /\ PoolCertificatesWellFormedOK
    /\ PoolAlignmentOK
    /\ BucketSlotConsistencyOK
    /\ PoolNotarFallbackBlockConsistencyOK
    /\ PoolSkipFallbackAfterInitialNotarOK
    /\ RotorSelectSoundness
    /\ TimeoutsInFuture
    /\ LocalClockMonotonic
    /\ UniqueBlockHashes(blocks)
    /\ AllBlocksValid(blocks)
    /\ (\A v \in Validators : UniqueBlocksPerSlot(finalized[v]))
    /\ FinalizedAncestorClosure
    /\ BlockNotarizedImpliesCert
    /\ ParentReadyImpliesCert
    /\ ParentReadyUsesPreviousBlock
    /\ FinalVoteImpliesBlockNotarized
    /\ VotedConsistency
    /\ ParentReadyConsistencyAll
    /\ PendingBlocksSingletonAll
    /\ PendingBlocksSlotAlignedAll
    /\ VotedNotarTagConsistency
    /\ BadWindowWitness
    /\ ItsOverWitness
    /\ TotalNotarStakeSanity
    /\ BoundedFinalization80
    /\ BoundedFinalization60

=============================================================================
