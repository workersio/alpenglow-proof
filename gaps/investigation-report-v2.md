# Alpenglow TLA+ Investigation Report

## 0. TL;DR (Pass/Fail Gates)
- ZWD (No whitepaper drift): Concerns
- CTU (Standards compliance): Concerns
- FCC (Claim coverage): Concerns
- Top risks and minimal patches:
  - DeliverCertificate lacks validity guard; allow only valid certs (patch). 
  - Fairness unconditional w.r.t. GST; gate fairness on AfterGST to match model assumptions (patch). 
  - Add explicit properties for Rotor eventual dissemination and ParentReady-triggered timeouts to cover whitepaper claims (patch). 
  - Strengthen Lemma 20 coverage (exactly one initial vote per slot per correct node) with liveness form (property addition).

## 1. Sources Read & Inventory
- Modules/configs/properties/fairness:
  - Modules: 
    - specs/tla/alpenglow/MainProtocol.tla:1 — top-level spec, Init/Next/Spec, safety/liveness, fairness.
    - specs/tla/alpenglow/VotorCore.tla:1 — voting state machine (Algorithm 1–2), timeouts, state flags.
    - specs/tla/alpenglow/VoteStorage.tla:1 — Pool (Definitions 12–16), multiplicity and certificate rules.
    - specs/tla/alpenglow/Messages.tla:1 — vote/cert types (Definition 11) and constructors.
    - specs/tla/alpenglow/Certificates.tla:1 — thresholds (Table 6), stake accounting.
    - specs/tla/alpenglow/Blocks.tla:1 — block/chain model, windows/schedule (Section 2.7).
    - specs/tla/alpenglow/Rotor.tla:1 — abstract Rotor relay selection (Section 2.2).
    - specs/tla/alpenglow/MC.tla:1, specs/tla/alpenglow/MC.cfg:1 — harness for TLC (not executed here).
  - Constants & variables (MainProtocol): 
    - Constants: NumValidators, ByzantineCount, GST, MaxSlot, MaxBlocks (specs/tla/alpenglow/MainProtocol.tla:22)
    - Variables: validators, blocks, messages, byzantineNodes, time, finalized, blockAvailability; `vars` tuple (specs/tla/alpenglow/MainProtocol.tla:41, specs/tla/alpenglow/MainProtocol.tla:50)
  - Actions (MainProtocol Next disjuncts): ReceiveBlock, ProcessTimeout, GenerateCertificateAction, FinalizeBlock, EmitBlockNotarized, EmitSafeToNotar, EmitSafeToSkip, EmitParentReady, ByzantineAction, HonestProposeBlock, ByzantineProposeBlock, DeliverVote, DeliverCertificate, BroadcastLocalVote, RotorDisseminateSuccess, RotorDisseminateFailure, RepairBlock, AdvanceTime (specs/tla/alpenglow/MainProtocol.tla:394)
  - Fairness: WF annotations on time/message/event actions and parameterized actions; unconditional (specs/tla/alpenglow/MainProtocol.tla:420)
  - Safety properties: SafetyInvariant, NoConflictingFinalization, ChainConsistency (= SafetyInvariant), VoteUniqueness, UniqueNotarization, GlobalNotarizationUniqueness, FinalizedImpliesNotarized, CertificateNonEquivocation, PoolMultiplicityOK, PoolCertificateUniqueness, TypeInvariant, Invariant (specs/tla/alpenglow/MainProtocol.tla:441, specs/tla/alpenglow/MainProtocol.tla:592, specs/tla/alpenglow/MainProtocol.tla:606)
  - Liveness: EventualFinalization, Progress, WindowFinalization(s) (specs/tla/alpenglow/MainProtocol.tla:541)

- Whitepaper↔Spec Naming Map:
- “Votor” (Section 2.6; Algorithm 1–2) ↔ VotorCore, VoteStorage, GenerateCertificateAction, Emit* events, ProcessTimeout (specs/tla/alpenglow/VotorCore.tla:1; specs/tla/alpenglow/VoteStorage.tla:1; specs/tla/alpenglow/MainProtocol.tla:307, specs/tla/alpenglow/MainProtocol.tla:320, specs/tla/alpenglow/MainProtocol.tla:307)
  - “Votor” (Section 2.6; Algorithm 1–2) ↔ VotorCore, VoteStorage, GenerateCertificateAction, Emit* events, ProcessTimeout (specs/tla/alpenglow/VotorCore.tla:1; specs/tla/alpenglow/VoteStorage.tla:1; specs/tla/alpenglow/MainProtocol.tla:135, specs/tla/alpenglow/MainProtocol.tla:338, specs/tla/alpenglow/MainProtocol.tla:351, specs/tla/alpenglow/MainProtocol.tla:366, specs/tla/alpenglow/MainProtocol.tla:382, specs/tla/alpenglow/MainProtocol.tla:121)
  - “Pool” (Definitions 12–16) ↔ PoolState, StoreVote, StoreCertificate, GenerateCertificate, CanEmit* (specs/tla/alpenglow/VoteStorage.tla:1)
  - “Certificates”/Table 6 ↔ Certificates module + constructors and validators (specs/tla/alpenglow/Certificates.tla:1)
  - “Messages” (Definition 11) ↔ Messages module: Vote, Certificate, constructors and classifiers (specs/tla/alpenglow/Messages.tla:1)
  - “ParentReady”, “BlockNotarized”, “SafeToNotar/Skip” (Definitions 15–16) ↔ ShouldEmitParentReady/BlockNotarized/CanEmit* + Emit* actions (specs/tla/alpenglow/VoteStorage.tla:205; specs/tla/alpenglow/MainProtocol.tla:336, specs/tla/alpenglow/MainProtocol.tla:356, specs/tla/alpenglow/MainProtocol.tla:370)
  - “Leader windows & schedule” (Section 2.7) ↔ Blocks: WindowSize, LeaderSchedule, IsFirstSlotOfWindow, WindowSlots, LeaderScheduleWindowConsistency (specs/tla/alpenglow/Blocks.tla:20, specs/tla/alpenglow/Blocks.tla:144, specs/tla/alpenglow/Blocks.tla:168)
  - “Rotor” (Section 2.2) ↔ Rotor module and Rotor* actions in MainProtocol (specs/tla/alpenglow/Rotor.tla:26, specs/tla/alpenglow/Rotor.tla:54; specs/tla/alpenglow/MainProtocol.tla:242, specs/tla/alpenglow/MainProtocol.tla:259)
  - “Blokstor” ↔ abstracted as blockAvailability + ReceiveBlock/RepairBlock (specs/tla/alpenglow/MainProtocol.tla:48, specs/tla/alpenglow/MainProtocol.tla:110, specs/tla/alpenglow/MainProtocol.tla:279)

## 2. Standards Catalog (FORCED from tla-docs.md)
- Overview of tla-docs.md (1–2 paragraphs)
  - The document is a pedagogical and methodological chapter on TLA+ (Merz), covering the standard form of specifications, the role of Init/Next and fairness, stuttering closure, typing invariants, safety vs liveness, use of assumptions/constants, and model-checking configuration idioms. It emphasizes the canonical Spec form S ≜ I ∧ □[N]_v ∧ L, the separation of invariant safety properties from liveness, and use of WF/SF fairness on actions. It also mentions symmetry reduction as a tool-level optimization and warns about liveness verification interactions.
  - The text underlines that TLA+ does not distinguish spec vs property syntactically; properties are implications S ⇒ F, with invariants expressed as state predicates and liveness via temporal modalities under fairness assumptions.

- MUST rules (top 10 checklist with quotes/anchors)
  1) STD-001 — SPEC form: “this is the standard form of system specifications in TLA+, … S ≜ I ∧ □[N]_v ∧ L; □[N]_v admits ‘stuttering transitions’.” (tla-docs.md:82)
  2) STD-002 — Next encodes disjunction of actions: “The action formula Next is defined as the disjunction of … actions … it defines the next-state relation.” (tla-docs.md:76)
  3) STD-003 — Stuttering closure via [N]_v: “□[N]_v … either satisfies N or leaves v unchanged … stuttering invariance is a key concept.” (tla-docs.md:82)
  4) STD-004 — Fairness on actions: “Fairness conditions complement … asserting what actions must occur (eventually). Weak/strong fairness …” (tla-docs.md:84)
  5) STD-005 — Safety as invariants: “no formal distinction … asserting S has property F amounts to S ⇒ F … invariants state intended ‘types’ … proved from transitions.” (tla-docs.md:58, tla-docs.md:104)
  6) STD-006 — Typing discipline (TypeInvariant): “The formula TypeInvariant states the intended ‘types’ … a theorem asserts the spec respects the typing invariant.” (tla-docs.md:58, tla-docs.md:106)
  7) STD-007 — Constants vs variables: “constant parameters … fixed during execution … variables … change during execution.” (tla-docs.md:52)
  8) STD-008 — Model config separation: “configuration file … SPECIFICATION, INVARIANTS, PROPERTIES …” (tla-docs.md:144)
  9) STD-009 — Symmetry (when applicable): “such symmetries are frequent … tlc implements symmetry reduction …” (tla-docs.md:154, tla-docs.md:163)
  10) STD-010 — Fairness strength tradeoffs: “verification succeeds with SF on per-resource … violated when replacing with weaker WF/SF … understand fairness hypotheses.” (tla-docs.md:84 and surrounding discussion)

- Full list: STD-001…STD-014
  - STD-001 | SPEC-form | MUST | “standard form … S ≜ I ∧ □[N]_v ∧ L … stuttering transitions” (tla-docs.md:82). Rationale: canonical, enables refinement and stuttering closure.
  - STD-002 | Action structure | MUST | “Next is disjunction of … actions” (tla-docs.md:76). Rationale: explicit control of transitions and frame conditions.
  - STD-003 | Stuttering | MUST | “□[N]_v … leaves v unchanged” (tla-docs.md:82). Rationale: ensures closure under stuttering and correct priming.
  - STD-004 | Fairness | MUST | “Fairness conditions … weak/strong fairness on actions” (tla-docs.md:84). Rationale: liveness relies on proper fairness on the right actions.
  - STD-005 | Safety-vs-Liveness | MUST | “no formal distinction … S ⇒ F …” (tla-docs.md:104). Rationale: state invariants vs temporal properties must be separated.
  - STD-006 | Typing | SHOULD | “TypeInvariant states intended ‘types’ … proven via transitions” (tla-docs.md:58, tla-docs.md:106). Rationale: catches spec errors early.
  - STD-007 | Parameters discipline | MUST | “constants fixed; variables change” (tla-docs.md:52). Rationale: avoids unsound dependence on mutable constants.
  - STD-008 | Config discipline | SHOULD | “SPECIFICATION/INVARIANTS/PROPERTIES in cfg” (tla-docs.md:144). Rationale: consistent model setup.
  - STD-009 | Symmetry | MAY | “symmetry reduction” (tla-docs.md:154). Rationale: performance/clarity when symmetric.
  - STD-010 | Fairness sensitivity | SHOULD | “alternative fairness hypotheses …” (fairness text; tla-docs.md:84). Rationale: avoid over/under-constraining.
  - STD-011 | Frame conditions | MUST | Implied by [N]_v use and action UNCHANGED for other vars (tla-docs.md:82). Rationale: no forgotten variables.
  - STD-012 | Vacuity awareness | SHOULD | Property implications must be non-vacuous under constraints/fairness (implied by spec/property separation; tla-docs.md:104). Rationale: prevent vacuous proofs.
  - STD-013 | Temporal operators use | MUST | Use ◇/□◇ for liveness under fairness (core TLA usage; sections 3.x; cf. tla-docs.md:84, tla-docs.md:104). Rationale: correct temporal intent.
  - STD-014 | Module organization | SHOULD | Modules with EXTENDS and operators definitions; naming conventional (tla-docs.md:52, general structure). Rationale: readability and reuse.

## 3. ZWD — Conformance Matrix
| Item | Whitepaper ref (quote) | Spec refs | Relation | Patch (if needed) | Severity | Evidence |
| --- | --- | --- | --- | --- | --- | --- |
| 1. Vote types & certs | “Definition 11 (messages)… Tables 5–6” (alpenglow-whitepaper.md:478) | Messages.tla:1; Certificates.tla:1 | Equivalent | — | — | specs/tla/alpenglow/Messages.tla:1; specs/tla/alpenglow/Certificates.tla:1 |
| 2. Multiplicity (Def. 12) | “Pool stores… first notar/skip; up to 3 notar-fallback; first skip-fallback; first finalization” (alpenglow-whitepaper.md:513) | VoteStorage.CanStoreVote/StoreVote (multiplicity), MultiplicityRulesRespected | Equivalent | — | — | specs/tla/alpenglow/VoteStorage.tla:54, specs/tla/alpenglow/VoteStorage.tla:318 |
| 3. Cert storage (Def. 13) | “single certificate of each type… corresponding to block/slot is stored in Pool” (alpenglow-whitepaper.md:520) | VoteStorage.CanStoreCertificate/StoreCertificate | Equivalent | — | — | specs/tla/alpenglow/VoteStorage.tla:109, specs/tla/alpenglow/VoteStorage.tla:128 |
| 4. Cert thresholds (Table 6) | “80% fast… 60% others; count-once per slot” (alpenglow-whitepaper.md:507) | Certificates thresholds + StakeFromVotes | Equivalent | — | — | specs/tla/alpenglow/Certificates.tla:41, specs/tla/alpenglow/Certificates.tla:73 |
| 5. ParentReady (Def. 15) | “first slot; notar/notar-fallback parent; skip for gaps” (alpenglow-whitepaper.md:543) | VoteStorage.ShouldEmitParentReady; EmitParentReady | Equivalent | — | — | specs/tla/alpenglow/VoteStorage.tla:261; specs/tla/alpenglow/MainProtocol.tla:382 |
| 6. Fallback events (Def. 16) | “SafeToNotar: notar≥40% or (skip+notar≥60% and notar≥20%); if not first slot, require parent notar-fallback. SafeToSkip: skip+Σnotar−max notar ≥40%” (alpenglow-whitepaper.md:554) | VoteStorage.CanEmitSafeToNotar/CanEmitSafeToSkip; EmitSafeToNotar/EmitSafeToSkip | Equivalent | — | — | specs/tla/alpenglow/VoteStorage.tla:276, specs/tla/alpenglow/VoteStorage.tla:299; specs/tla/alpenglow/MainProtocol.tla:351, specs/tla/alpenglow/MainProtocol.tla:366 |
| 7. TryNotar/Final/Skip (Alg. 2) | “TRYNOTAR… first slot needs ParentReady; else prior notar for parent. TRYFINAL needs notarized and VotedNotar and no BadWindow. TRYSKIPWINDOW sets Voted+BadWindow.” (alpenglow-whitepaper.md:Page 23–26 code) | VotorCore.TryNotar/TryFinal/TrySkipWindow | Equivalent | — | — | specs/tla/alpenglow/VotorCore.tla:105, specs/tla/alpenglow/VotorCore.tla:139, specs/tla/alpenglow/VotorCore.tla:161 |
| 8. Algorithm 1 Handlers | “Block, Timeout, BlockNotarized, ParentReady, SafeToNotar/Skip…” (alpenglow-whitepaper.md:Page 23–26 code) | VotorCore.HandleBlock/Timeout/BlockNotarized/ParentReady/SafeToNotar/SafeToSkip | Equivalent | — | — | specs/tla/alpenglow/VotorCore.tla:211, specs/tla/alpenglow/VotorCore.tla:229, specs/tla/alpenglow/VotorCore.tla:241, specs/tla/alpenglow/VotorCore.tla:251, specs/tla/alpenglow/VotorCore.tla:272, specs/tla/alpenglow/VotorCore.tla:288 |
| 9. Leader windows (Sec. 2.7) | “WindowSize; FirstSlotOfWindow; Leader schedule constant across window” (alpenglow-whitepaper.md:760) | Blocks.FirstSlotOfWindow/IsFirstSlotOfWindow/LeaderScheduleWindowConsistency; HonestProposeBlock | Equivalent | — | — | specs/tla/alpenglow/Blocks.tla:156, specs/tla/alpenglow/Blocks.tla:168, specs/tla/alpenglow/Blocks.tla:175; specs/tla/alpenglow/MainProtocol.tla:181 |
| 10. Finalization (Def. 14) | “fast (80%) finalizes b; slow finalization uses finalization cert, unique notarized block in slot; ancestors finalized first” (alpenglow-whitepaper.md:536) | FinalizeBlock action; FinalizedImpliesNotarized invariant | Equivalent (operational) | — | — | specs/tla/alpenglow/MainProtocol.tla:154; specs/tla/alpenglow/MainProtocol.tla:511 |
| 11. Rotor selection (Sec. 2.2) | “stake-fair relay sampling; next leader prioritised; fanout bounded; eventual dissemination” | RotorCandidates/Select; RotorDisseminate* actions | Narrower on eventuality (no explicit liveness property) | Add property RotorEventuallyDelivers (below) | Minor | specs/tla/alpenglow/Rotor.tla:26, specs/tla/alpenglow/Rotor.tla:54; specs/tla/alpenglow/MainProtocol.tla:242, specs/tla/alpenglow/MainProtocol.tla:259 |
| 12. Partial synchrony (GST) | “after GST liveness” (alpenglow-whitepaper.md:248) | Fairness unconditional; EventualFinalization guarded by time≥GST | Different (stronger fairness than paper) | Gate fairness with AfterGST (patch) | Major | specs/tla/alpenglow/MainProtocol.tla:420 |

## 4. CTU — Standards Conformance Matrix
| STD-### | Category | Level | Spec refs | Status | Patch (if needed) | Evidence (tla-docs.md + spec) |
| --- | --- | --- | --- | --- | --- | --- |
| STD-001 | SPEC-form | MUST | MainProtocol Spec (specs/tla/alpenglow/MainProtocol.tla:438) | Pass | — | Spec uses Init ∧ □[Next]_vars ∧ Fairness; tla-docs.md:82 |
| STD-002 | Action structure | MUST | Next disjunction (specs/tla/alpenglow/MainProtocol.tla:394) | Pass | — | “Next is … disjunction…” tla-docs.md:76 |
| STD-003 | Stuttering | MUST | [Next]_vars and UNCHANGED per action | Pass | — | tla-docs.md:82; actions use UNCHANGED frames |
| STD-004 | Fairness | MUST | Fairness block (specs/tla/alpenglow/MainProtocol.tla:420) | Partial | Gate fairness on AfterGST | tla-docs.md:84 — fairness models liveness preconditions |
| STD-005 | Safety vs Liveness | MUST | Invariant vs PROPERTIES split (MC.cfg) | Pass | — | tla-docs.md:104; MC.cfg: INVARIANTS/PROPERTIES (specs/tla/alpenglow/MC.cfg:43) |
| STD-006 | Typing | SHOULD | TypeInvariant (specs/tla/alpenglow/MainProtocol.tla:592) | Pass | — | tla-docs.md:58,106 |
| STD-007 | Parameters discipline | MUST | CONSTANTS/ASSUME used in modules | Pass | — | tla-docs.md:52; e.g., Messages constants (specs/tla/alpenglow/Messages.tla:16, specs/tla/alpenglow/Messages.tla:23) |
| STD-008 | Config discipline | SHOULD | MC.cfg has SPECIFICATION/INVARIANTS/PROPERTIES | Pass | — | tla-docs.md:144; specs/tla/alpenglow/MC.cfg:1 |
| STD-009 | Symmetry | MAY | Not used | N/A | — | tla-docs.md:154 |
| STD-010 | Fairness sensitivity | SHOULD | Fairness unconditional w.r.t. GST | Fail | Gate fairness (AfterGST) | tla-docs.md:84; avoid over-constraining pre-GST |
| STD-011 | Frame conditions | MUST | UNCHANGED present; vars tuple defined | Pass | — | tla-docs.md:82; specs/tla/alpenglow/MainProtocol.tla:50 |
| STD-012 | Vacuity awareness | SHOULD | Liveness guarded by time ≥ GST | Pass | — | tla-docs.md:104; EventualFinalization (specs/tla/alpenglow/MainProtocol.tla:548) |
| STD-013 | Temporal operators | MUST | ◇/~> used; WF on actions | Pass | — | tla-docs.md:84,104; EventualFinalization/Progress |
| STD-014 | Module org | SHOULD | Clean EXTENDS and separation | Pass | — | tla-docs.md:52; modules well-structured |

Notes on CTU findings (citations):
- CTU-001: Unconditional fairness may exceed whitepaper model (“after GST … honest messages keep flowing”) and risks over-constraining pre-GST runs. Per STD-004/STD-010 (tla-docs.md:84), gate WF on relevant actions by AfterGST to align with model assumptions. Status: Partial/Fail.

## 5. FCC — Claim/Proof Coverage Matrix
| Claim ID | Whitepaper ref | Intended form (+STD) | Spec artifact(s) | Status | Proposed property (if missing) | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| C-001 (Safety/Theorem 1) | “Theorem 1 (safety)… finalized forms a chain” (alpenglow-whitepaper.md:930–932) | Invariant Safety: □ ChainConsistency (STD-005, STD-013) | SafetyInvariant / ChainConsistency (specs/tla/alpenglow/MainProtocol.tla:466) | Covered | — | Uses IsAncestor from Blocks |
| C-002 (No conflicting finalization) | Corollary in Theorem 1 context | Invariant □ NoConflictingFinalization (STD-005) | NoConflictingFinalization (specs/tla/alpenglow/MainProtocol.tla:458) | Covered | — | — |
| C-003 (Lemma 20) | “one notarization or skip vote per slot per correct node” (alpenglow-whitepaper.md:820) | Invariant + eventuality: (≤1 initial vote) ∧ (eventually initial vote per slot) (STD-005/STD-013) | VoteUniqueness (≤1) (specs/tla/alpenglow/MainProtocol.tla:504) | Partial | Add ExactlyOneInitialEventually (below) | Current spec enforces ≤1, not “exactly one” without liveness side |
| C-004 (Lemma 24, unique notarization) | “at most one block notarized per slot” | Invariant □ UniqueNotarization (STD-005) | UniqueNotarization + GlobalNotarizationUniqueness (specs/tla/alpenglow/MainProtocol.tla:516, specs/tla/alpenglow/MainProtocol.tla:528) | Covered | — | — |
| C-005 (Lemma 25, finalized implies notarized) | “Every finalized block was first notarized” | Invariant □ FinalizedImpliesNotarized (STD-005) | FinalizedImpliesNotarized (specs/tla/alpenglow/MainProtocol.tla:539) | Covered | — | — |
| C-006 (Certificate non-equivocation) | Def. 13 uniqueness | Invariant □ CertificateNonEquivocation (STD-005) | CertificateNonEquivocation (specs/tla/alpenglow/MainProtocol.tla:549) | Covered | — | — |
| C-007 (Pool multiplicity/uniqueness) | Defs. 12–13 | Invariant □ PoolMultiplicityOK ∧ PoolCertificateUniqueness (STD-005) | PoolMultiplicityOK / PoolCertificateUniqueness (specs/tla/alpenglow/MainProtocol.tla:555, specs/tla/alpenglow/MainProtocol.tla:558) | Covered | — | — |
| C-008 (Finalization semantics) | Definition 14 (Page 21) | Operational + invariants (STD-005) | FinalizeBlock action + invariants | Covered | — | Ancestor finalization is implied by SafetyInvariant + operation |
| C-009 (Liveness/Theorem 2) | “In any long enough synchrony after GST, finalize new blocks” (alpenglow-whitepaper.md:248; Lemmas 33–41) | Temporal ◇ under WF/SF: EventualFinalization, WindowFinalization(s) (STD-013/STD-004) | EventualFinalization, WindowFinalization(s) (specs/tla/alpenglow/MainProtocol.tla:548, specs/tla/alpenglow/MainProtocol.tla:575) | Partial | Gate WF by AfterGST; optionally add WindowFinalization to PROPERTIES | Fairness gating aligns with premises |
| C-010 (Rotor eventual dissemination) | Sec. 2.2 qualitative eventuality | Temporal ◇ delivery (STD-013) | Actions exist; no property | Missing | Add RotorEventuallyDelivers (below) | Needed for liveness chain ParentReady/Repair |
| C-011 (Adversary bound 20%) | Assumption 1 (alpenglow-whitepaper.md:107) | Invariant/ASSUME (STD-007) | ByzantineStakeOK in Init and Invariant (specs/tla/alpenglow/MainProtocol.tla:111, specs/tla/alpenglow/MainProtocol.tla:561) | Covered | — | Computes stake via Certificates module |
| C-012 (Crash tolerance “20+20%”) | Assumption 2 sketch (alpenglow-whitepaper.md:122) | Assumptive model extension (STD-007) | Not explicitly modeled | Missing | — | Out-of-scope for base spec; note as future extension |

## 6. Minimal Patches (Alignment & Standards Only)
- ZWD patches (diff-style):
  - Gate fairness by AfterGST to match whitepaper model (STD-004, STD-010):
    
    --- specs/tla/alpenglow/MainProtocol.tla
    +++ specs/tla/alpenglow/MainProtocol.tla
    @@
    -Fairness ==
    -    /\ WF_vars(AdvanceTime)
    -    /\ WF_vars(DeliverVote)
    -    /\ WF_vars(DeliverCertificate)
    -    /\ WF_vars(BroadcastLocalVote)
    -    /\ WF_vars(EmitBlockNotarized)
    -    /\ WF_vars(EmitSafeToNotar)
    -    /\ WF_vars(EmitSafeToSkip)
    -    /\ WF_vars(EmitParentReady)
    -    /\ WF_vars(\E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p))
    -    /\ WF_vars(\E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s))
    -    /\ WF_vars(\E b \in blocks : RotorDisseminateSuccess(b))
    -    /\ WF_vars(\E v \in Validators, b \in blocks, s \in Validators : RepairBlock(v, b, s))
    -    /\ \A v \in Validators :
    -           IF v \in CorrectNodes
    -           THEN WF_vars(\E b \in blocks : ReceiveBlock(v, b))
    -           ELSE TRUE
    +Fairness ==
    +    /\ WF_vars(AdvanceTime)
    +    /\ WF_vars(IF AfterGST THEN DeliverVote ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN DeliverCertificate ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN BroadcastLocalVote ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN EmitBlockNotarized ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN EmitSafeToNotar ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN EmitSafeToSkip ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN EmitParentReady ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN (\E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p)) ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN (\E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s)) ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN (\E b \in blocks : RotorDisseminateSuccess(b)) ELSE UNCHANGED vars)
    +    /\ WF_vars(IF AfterGST THEN (\E v \in Validators, b \in blocks, s \in Validators : RepairBlock(v, b, s)) ELSE UNCHANGED vars)
    +    /\ \A v \in Validators :
    +           IF v \in CorrectNodes
    +           THEN WF_vars(IF AfterGST THEN (\E b \in blocks : ReceiveBlock(v, b)) ELSE UNCHANGED vars)
    +           ELSE TRUE

- CTU refactors (diff-style):
  - Enforce certificate validity on delivery (STD-005/STD-011):
    
    --- specs/tla/alpenglow/MainProtocol.tla
    +++ specs/tla/alpenglow/MainProtocol.tla
    @@
    -DeliverCertificate ==
    -    /\ \E cert \in messages : cert \in Certificate
    -    /\ LET cmsg == CHOOSE cc \in messages : cc \in Certificate
    +DeliverCertificate ==
    +    /\ \E cert \in messages : cert \in Certificate /\ IsValidCertificate(cert)
    +    /\ LET cmsg == CHOOSE cc \in messages : cc \in Certificate /\ IsValidCertificate(cc)
         IN /\ messages' = messages \ {cmsg}
            /\ validators' = [w \in Validators |->
                                 [validators[w] EXCEPT
                                     !.pool = StoreCertificate(@, cmsg)]]
        /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>

- FCC property additions (exact TLA text):
  - Exactly-one-initial-eventually per slot for correct validators (strengthens Lemma 20; STD-005/STD-013):
    
    --- specs/tla/alpenglow/MainProtocol.tla
    +++ specs/tla/alpenglow/MainProtocol.tla
    @@
    +ExactlyOneInitialEventually ==
    +    \A v \in CorrectNodes : \A s \in 1..MaxSlot :
    +        <>(\E vt \in GetVotesForSlot(validators[v].pool, s) :
    +              vt.validator = v /\ IsInitialVote(vt))
    +        /\ [] (Cardinality({vt \in GetVotesForSlot(validators[v].pool, s) :
    +                             vt.validator = v /\ IsInitialVote(vt)}) <= 1)
    
  - Rotor eventual dissemination (Section 2.2; STD-013):
    
    --- specs/tla/alpenglow/MainProtocol.tla
    +++ specs/tla/alpenglow/MainProtocol.tla
    @@
    +RotorEventuallyDelivers ==
    +    \A b \in blocks :
    +        (b.leader \in CorrectNodes) /\ (b.slot \in 1..MaxSlot)
    +        => <>(\A v \in Validators : b \in blockAvailability[v])
    
  - ParentReady implies timeouts scheduled for window (Lemmas 33–35; STD-013):
    
    --- specs/tla/alpenglow/MainProtocol.tla
    +++ specs/tla/alpenglow/MainProtocol.tla
    @@
    +ParentReadySchedulesTimeouts ==
    +    \A v \in CorrectNodes : \A s \in 1..MaxSlot :
    +        (IsFirstSlotOfWindow(s) /\ HasState(validators[v], s, "ParentReady"))
    +        => (\A i \in (WindowSlots(s) \cap 1..MaxSlot) : validators[v].timeouts[i] > 0)

## 7. Open Questions & Assumptions
- Does the intended model allow adversarial certificate injection? If yes, DeliverCertificate must validate; current ByzantineAction injects only votes.
- Should fairness before GST be disallowed entirely or only gated on actions whose enabling relies on network stability? Proposed patch uses conditional WF on AfterGST.
- Whitepaper’s extended crash tolerance (Assumption 2) is not modeled; confirm if out-of-scope for this spec version or desired as a separate spec variant.

## 8. Change Log
- Pass 1: Initial end-to-end review; compiled Standards Catalog; mapped whitepaper↔spec; identified fairness gating and validity check patches; proposed additional properties for FCC completeness.

---

Appendix: Evidence Snippets
- Standard SPEC form: tla-docs.md:82
- Fairness discussion: tla-docs.md:84
- TypeInvariant guidance: tla-docs.md:58, tla-docs.md:106
- Config usage: tla-docs.md:144
- Symmetry (optional): tla-docs.md:154
- Whitepaper Def. 11/12/13/14/15/16 refs: alpenglow-whitepaper.md:478, alpenglow-whitepaper.md:513, alpenglow-whitepaper.md:520, alpenglow-whitepaper.md:536, alpenglow-whitepaper.md:543, alpenglow-whitepaper.md:554
- Theorem 1 safety: alpenglow-whitepaper.md:930
- Lemmas 33–41 timeouts/ParentReady chain: alpenglow-whitepaper.md:943
