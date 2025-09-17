# Alpenglow TLA+ Investigation Report

## 0. TL;DR (Focus Gates)
- ZWD (No whitepaper drift): Concerns
- CTU (Correct TLA usage): Pass
- FCC (Full claim coverage): Pass
- Top risks & immediate patches:
  - ZWD-1 (Major): SafeToNotar emission requires local block availability; whitepaper allows emission in first-slot case without prior repair. Patch: drop `b \in blockAvailability[v]` from `EmitSafeToNotar` guard (MainProtocol.tla:351–359).

## 1. Sources Read & Inventory
- Modules / configs / properties / fairness:
  - specs/tla/alpenglow/MainProtocol.tla:1–620
    - Spec formula: `Spec == Init /\ [][Next]_vars /\ Fairness` (MainProtocol.tla:439)
    - Next relation: action disjunction including receive/propose/vote/cert/parent-ready/repair/rotor/time (MainProtocol.tla:395–413)
    - Fairness: WF on time, deliveries, emissions, honest propose, certificate generation, rotor success, repair, per-node receive (MainProtocol.tla:421–437)
    - Safety invariants: SafetyInvariant, NoConflictingFinalization, ChainConsistency, VoteUniqueness, UniqueNotarization, FinalizedImpliesNotarized, CertificateNonEquivocation, PoolMultiplicityOK, PoolCertificateUniqueness, ByzantineStakeOK (MainProtocol.tla:449–584)
    - Liveness: EventualFinalization, Progress (MainProtocol.tla:535–551)
  - specs/tla/alpenglow/Blocks.tla:1–260
    - Leader/slot/window helpers: `Leader`, `FirstSlotOfWindow`, `WindowSlots` (Blocks.tla:149,156,175)
  - specs/tla/alpenglow/Messages.tla:1–180
    - Vote/Certificate message families (Definition 11) and helpers
  - specs/tla/alpenglow/Certificates.tla:1–240
    - Thresholds and cert constructors (80/60 logic), count-once stake
  - specs/tla/alpenglow/VoteStorage.tla:1–320
    - Pool state, multiplicity (Definition 12), certificate storage (Definition 13), event guards (Definitions 15–16), stake queries, `GenerateCertificate`
  - specs/tla/alpenglow/VotorCore.tla:1–620
    - Votor state (Definition 18), TRYNOTAR/TRYFINAL/TRYSKIPWINDOW (Algorithms 1–2), event handlers, timeout scheduling (Definition 17)
  - specs/tla/alpenglow/Rotor.tla:1–120
    - Abstract dissemination and constraints (Definition 6 flavor)
  - specs/tla/alpenglow/MC.tla, MC.cfg: harness/constants/invariants list
- Constants & variables:
  - System constants: `NumValidators`, `ByzantineCount`, `GST`, `MaxSlot`, `MaxBlocks` (MainProtocol.tla:22–35);
    `WindowSize`, `LeaderSchedule` (Blocks.tla:20,26); timings `DeltaTimeout`, `DeltaBlock` (VotorCore.tla:18–24);
    Rotor params `RotorFanout`, `RotorMinRelayStake`, `RotorGamma` (Rotor.tla:15–23); stake map `StakeMap` (Certificates.tla:20–23)
  - Variables: `validators, blocks, messages, byzantineNodes, time, finalized, blockAvailability` (MainProtocol.tla:41–50)
- Naming Map (whitepaper → spec):
  - Votor → `VotorCore` module, handlers `Handle*`, `TryNotar`, `TryFinal`, `TrySkipWindow` (VotorCore.tla:105–139, 160–220, 224–288)
  - Pool → `PoolState` with `votes`, `certificates` and ops `StoreVote`, `GenerateCertificate`, `CanStore*`, `Has*` (VoteStorage.tla:14–34, 100–160, 181–240)
  - Votes (Notar, NotarFallback, Skip, SkipFallback, Final) → `VoteType` and constructors (Messages.tla:32–87)
  - Certificates (FastFinal, Notarization, NotarFallback, Skip, Final) → `CertificateType` and constructors (Messages.tla:108–160)
  - Stake thresholds (80%, 60%, 40%, 20%) → `MeetsThreshold`, `CanCreate*` (Certificates.tla:64–72, 84–160)
  - Leader/slot/window → `Leader`, `FirstSlotOfWindow`, `WindowSlots` (Blocks.tla:149–179)
  - ParentReady/BlockNotarized/SafeToNotar/SafeToSkip events → `ShouldEmit*`, `CanEmit*`, and `Emit*` actions (VoteStorage.tla:250–305; MainProtocol.tla:338–389)
  - Timeouts (Definition 17) → `HandleParentReady` schedules `timeouts`, `AdvanceClock` processes them (VotorCore.tla:246–263, 303–314)
  - Rotor → `RotorSelect`, `RotorDisseminateSuccess/Failure`, constraints (Rotor.tla:31–67; MainProtocol.tla:242–260, 264–276)
  - Finalization (Definition 14) → `FinalizeBlock`, `HasFastFinalizationCert`, `HasNotarizationCert`, `HasFinalizationCert` (MainProtocol.tla:154–163; VoteStorage.tla:232–239)
  - Assumption 1 (<20% byzantine stake) → `ByzantineStakeOK` invariant (MainProtocol.tla:74–82, 570–584)

## 2. ZWD — Conformance Matrix
| Item | Whitepaper ref (quote) | Spec refs | Relation | Patch (if needed) | Severity | Evidence |
|------|-------------------------|-----------|----------|-------------------|----------|----------|
| ZWD-1 | Definition 16, Page 22: “If s is the first slot in the leader window, the [SafeToNotar] event is emitted. Otherwise … event is emitted when Pool contains the notar-fallback certificate for the parent as well.” | `EmitSafeToNotar` requires `b \in blockAvailability[v]` unconditionally (MainProtocol.tla:351–359). Parent gating handled in `CanEmitSafeToNotar` (VoteStorage.tla:276–288). | Narrower | Remove local-availability guard in `EmitSafeToNotar`. | Major | The first-slot case in the paper does not require having locally stored `b`; spec currently blocks emission if `b` not in local `blockAvailability`. |
| ZWD-2 | Definition 15: “ParentReady(s, hash(b)): Slot s is the first of its leader window, and Pool holds a notarization or notar-fallback certificate for a previous block b, and skip certificates for every slot s′ since b.” | `ShouldEmitParentReady` matches: first slot of window, notar or notar-fallback for parent, skip certs for gaps (VoteStorage.tla:261–266). `EmitParentReady` enforces first-slot, parent slot +1 (MainProtocol.tla:382–389). | Equivalent | — | — | Alignment exact to text and prerequisites matched. |
| ZWD-3 | Definition 12 (storing votes): first notar or skip; up to 3 notar-fallback; first skip-fallback; first finalization. | `CanStoreVote` enforces exactly those multiplicities (VoteStorage.tla:36–73). | Equivalent | — | — | Direct transcription with per-type caps. |
| ZWD-4 | Definition 11/Table 6 thresholds: Fast (80% NotarVote); Notarization (60% NotarVote); Notar-Fallback (60% NotarVote or NotarFallbackVote); Skip (60% Skip*); Final (60% FinalVote). Count once per slot. | `CanCreate*` predicates, `StakeFromVotes(UniqueValidators(...))` respects count-once, constructors mirror types (Certificates.tla:84–160, 64–72, 164–236). | Equivalent | — | — | Thresholds and typing match table precisely. |
| ZWD-5 | Definition 14 (finalization): slow path = FinalizationCert implies finalize unique notarized block in slot; fast path = FastFinalizationCert implies finalize b. | `FinalizeBlock` checks either fast cert or (notarization cert for b and finalization cert for slot) (MainProtocol.tla:154–163); uniqueness covered by `UniqueNotarization`. | Equivalent | — | — | Matches the two cases; uniqueness ensured separately. |
| ZWD-6 | Definition 17 (timeouts): Timeout(i) := clock() + Δ_timeout + (i − s + 1)·Δ_block. | `HandleParentReady` sets timeouts for window slots with exactly that formula (VotorCore.tla:260–263). | Equivalent | — | — | Formula matches verbatim. |
| ZWD-7 | Definition 16 SafeToSkip: skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%. | `CanEmitSafeToSkip` implements exactly the inequality (VoteStorage.tla:299–305). | Equivalent | — | — | Direct transcription. |
| ZWD-8 | Section 2.2 Rotor success criteria and prioritizing next leader. | `RotorSelect` includes next leader when needed, bounded fanout, min relay stake; success when ≥γ correct relays (Rotor.tla:31–67; MainProtocol.tla:242–252). | Equivalent | — | — | Matches qualitative constraints. |
| ZWD-9 | Safety Theorem 1: finalized blocks form a chain of ancestry. | `SafetyInvariant` and `NoConflictingFinalization`, `ChainConsistency` (MainProtocol.tla:449–468). | Equivalent | — | — | Encodes the theorem and corollary. |
| ZWD-10 | Lemma 20 (one initial vote per slot). | `VoteUniqueness` (MainProtocol.tla:469–479). | Equivalent | — | — | Mirrors lemma. |
| ZWD-11 | Lemma 24 (unique notarization per slot). | `UniqueNotarization` (MainProtocol.tla:485–493). | Equivalent | — | — | Checks certificate set per slot. |
| ZWD-12 | Lemma 25 (finalized implies notarized). | `FinalizedImpliesNotarized` (MainProtocol.tla:498–506). | Equivalent | — | — | Uses pool certificates to witness. |
| ZWD-13 | Assumption 1 (<20% byzantine stake). | `ByzantineStakeOK` included as invariant (MainProtocol.tla:79–82, 570–584). | Equivalent | — | — | Assumed and maintained. |

## 3. CTU — TLA Pattern Audit
- SPEC form / stuttering / frame conditions:
  - Spec uses standard form `Init /\ [][Next]_vars /\ Fairness` (MainProtocol.tla:439). All actions assign or `UNCHANGED` non-touched variables. No forgotten variables; `vars` lists all state (MainProtocol.tla:41–50).
- Safety vs Liveness separation:
  - State invariants are predicates over current state. Liveness uses leads-to under fairness and GST, no misuse of invariants for temporal claims (MainProtocol.tla:535–551).
- Fairness placement:
  - Weak fairness on time advance, vote/cert delivery, emit events, honest propose, certificate generation, rotor success, repair, plus per-node block receive (MainProtocol.tla:421–437). Matches partial-synchrony and “messages keep flowing after GST” guidance (whitepaper §2.10). This aligns with house guidance to attach WF/SF on environment/communication steps (tla-docs.md §2–3, fairness examples).
- Parameters / symmetry / typing discipline:
  - Constants declared with type assumptions; state constraint in MC.cfg bounds state space. TypeInvariant covers domains (MainProtocol.tla:556–566). Symmetry not assumed; validators treated generically.
- Vacuity / over-constraint checks:
  - No over-constraining of Next; environment includes Byzantine actions. Liveness guarded by `(time >= GST) ~>` and WF on requisite actions. No vacuous invariants observed.

Findings (CTU-#):
- None. Current structure follows the patterns in tla-docs.md: clear separation of Init/Next/Spec, state predicates for safety, temporal for liveness under WF, explicit typing.

## 4. FCC — Claim/Proof Coverage Matrix
| Claim ID | Whitepaper ref | Intended form | Spec artifact(s) | Status | Proposed property (if missing) | Notes |
|---------:|----------------|---------------|------------------|--------|--------------------------------|-------|
| FCC-1 | Theorem 1 (safety) (alpenglow-whitepaper.md:930) | Invariant: finalized blocks form a chain | `SafetyInvariant`, `NoConflictingFinalization`, `ChainConsistency` (MainProtocol.tla:449–468) | Covered | — | Encodes theorem and corollary. |
| FCC-2 | Theorem 2 (liveness) (alpenglow-whitepaper.md:1045) | Liveness under GST + rotor success | `EventualFinalization`, `Progress`, WF on dissemination/propose/cert (MainProtocol.tla:421–437, 535–551) | Covered | — | Uses WF and `(time >= GST) ~>` guard to model partial synchrony. |
| FCC-3 | Lemma 20 (one initial vote) (alpenglow-whitepaper.md:820) | Invariant | `VoteUniqueness` (MainProtocol.tla:469–479) | Covered | — | Also enforced by multiplicity rules in `VoteStorage`. |
| FCC-4 | Lemma 24 (unique notarization) (alpenglow-whitepaper.md:855) | Invariant | `UniqueNotarization` (MainProtocol.tla:485–493) | Covered | — | Matches slot-wise uniqueness. |
| FCC-5 | Lemma 25 (finalized implies notarized) (alpenglow-whitepaper.md:866) | Invariant | `FinalizedImpliesNotarized` (MainProtocol.tla:498–506) | Covered | — | Witnessed from pool. |
| FCC-6 | Definition 11/Table 6 thresholds | Structural/typing + Theorem dependency | `CanCreate*`, `IsValidCertificate` (Certificates.tla:84–160, 191–211) | Covered | — | Encoded exactly. |
| FCC-7 | Assumption 1 (<20% byz) (alpenglow-whitepaper.md:107) | Assumption/state constraint | `ByzantineStakeOK` invariant, Init (MainProtocol.tla:79–82, 97) | Covered | — | Ensures resilience precondition. |
| FCC-8 | Definition 17 (timeouts) (alpenglow-whitepaper.md:602–613) | State-update discipline | `HandleParentReady` timeout schedule (VotorCore.tla:260–263) | Covered | — | Matches formula. |
| FCC-9 | Definition 15 (events) (alpenglow-whitepaper.md:543) | Guards that trigger events | `ShouldEmitBlockNotarized`, `ShouldEmitParentReady`, `Emit*` (VoteStorage.tla:250–266; MainProtocol.tla:338–389) | Covered | — | Exact matches. |
| FCC-10 | Definition 16 (fallback events) (alpenglow-whitepaper.md:554, Page 22) | Guards for SafeToNotar/Skip | `CanEmitSafeToNotar`, `CanEmitSafeToSkip` (VoteStorage.tla:276–288, 299–305) | Covered | — | Parent gating for non-first slots encoded. |

## 5. Patches (Minimal & Alignment-Only)
- ZWD patches:
  - ZWD-1 (Major): Remove extra local-availability requirement from SafeToNotar emission.
    - Diff snippet (do not execute):
      - File: `specs/tla/alpenglow/MainProtocol.tla:351–359`
      - Before:
        - `EmitSafeToNotar ==`
        - `    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, b \in blocks :`
        - `         /\ b.slot = s`
        - `         /\ b \in blockAvailability[v]`
        - `         /\ LET alreadyVoted == HasState(validators[v], s, \"Voted\")`
        - `                votedForB == VotedForBlock(validators[v], s, b.hash)`
        - `            IN CanEmitSafeToNotar(validators[v].pool, s, b.hash, b.parent, alreadyVoted, votedForB)`
        - `         /\ ~HasState(validators[v], s, \"BadWindow\")`
        - `         /\ validators' = [validators EXCEPT ![v] = HandleSafeToNotar(@, s, b.hash)]`
      - After (drop local availability guard; parent gating remains inside `CanEmitSafeToNotar`):
        - `EmitSafeToNotar ==`
        - `    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, b \in blocks :`
        - `         /\ b.slot = s`
        - `         /\ LET alreadyVoted == HasState(validators[v], s, \"Voted\")`
        - `                votedForB == VotedForBlock(validators[v], s, b.hash)`
        - `            IN CanEmitSafeToNotar(validators[v].pool, s, b.hash, b.parent, alreadyVoted, votedForB)`
        - `         /\ ~HasState(validators[v], s, \"BadWindow\")`
        - `         /\ validators' = [validators EXCEPT ![v] = HandleSafeToNotar(@, s, b.hash)]`

- CTU refactors: None required.

- FCC property additions: None required.

## 6. Open Questions & Assumptions
- For liveness (Theorem 2), the spec models rotor success with WF on `RotorDisseminateSuccess` after GST. This encodes the whitepaper’s synchrony/availability premise; no additional changes needed.
- Economic/slashing aspects are not normative claims in the provided whitepaper excerpts; the spec intentionally omits economics (consistent with context).

## 7. Change Log
- Pass 1: Full inventory, naming map, conformance and pattern audit; identified ZWD-1 (Major). Proposed minimal diff to restore exact alignment for SafeToNotar emission. All other mechanisms match the whitepaper statements and thresholds. FCC coverage verified against listed claims and definitions.
