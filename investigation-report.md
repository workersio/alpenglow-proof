# Alpenglow TLA+ Investigation Report

## 0. TL;DR (Focus Gates)
- ZWD (No whitepaper drift): Minor drift
 - CTU (Correct TLA usage): Pass
- FCC (Full claim coverage): Concerns
- Top risks & immediate patches:
  - ZWD-1 (Major, Open): SafeToNotar over-constrained by local block availability. Patch: drop `b \in blockAvailability[v]` from `EmitSafeToNotar` (specs/tla/alpenglow/MainProtocol.tla:351). Whitepaper Definition 16 allows first-slot emission without repair.
  - ZWD-2 (Major, Open): ParentReady incorrectly restricted to immediate predecessor slot (`p.slot + 1 = s`). Patch: remove that guard in `EmitParentReady` (specs/tla/alpenglow/MainProtocol.tla:382). Definition 15 allows earlier notarized parent bridged by skip certs.
  - FCC-11 (Major, Open): Lemma 24 global uniqueness not fully captured (per-node only). Add cross-validator uniqueness covering both Notarization and NotarFallback certificates.
  - FCC-12 (Major, Open): Theorem 2’s per-window finalization liveness not explicitly captured. Add a window-scoped liveness property under stated assumptions (GST, correct window leader, no pre-GST timeouts, Rotor success).

- Note: ZWD-1 was rescinded after cross-checking Definition 10 (Blokstor). See ZWD-1 row (Resolved).

## 1. Sources Read & Inventory
- Modules / configs / properties / fairness:
  - specs/tla/alpenglow/MainProtocol.tla:1
    - Spec formula: `Spec == Init /\ [][Next]_vars /\ Fairness` (specs/tla/alpenglow/MainProtocol.tla:439)
    - Next relation: block receive, timeouts, certificate generation, finalization, event emissions, Byzantine action, honest/byz propose, dissemination, repair, time advance (specs/tla/alpenglow/MainProtocol.tla:395)
    - Fairness: WF on time advance, vote/certificate delivery, event emissions, honest propose, certificate generation, Rotor success, repair, and per-validator receive (specs/tla/alpenglow/MainProtocol.tla:421)
    - Safety invariants: `SafetyInvariant`, `NoConflictingFinalization`, `ChainConsistency`, `VoteUniqueness`, `UniqueNotarization`, `FinalizedImpliesNotarized`, `CertificateNonEquivocation`, `PoolMultiplicityOK`, `PoolCertificateUniqueness`, `ByzantineStakeOK` (specs/tla/alpenglow/MainProtocol.tla:449)
    - Liveness: `EventualFinalization`, `Progress` (specs/tla/alpenglow/MainProtocol.tla:535)
  - specs/tla/alpenglow/Blocks.tla:1
    - Chain and window helpers: `Leader`, `FirstSlotOfWindow`, `IsFirstSlotOfWindow`, `WindowSlots` (specs/tla/alpenglow/Blocks.tla:149, 156, 161, 175)
  - specs/tla/alpenglow/Messages.tla:1
    - Votes, certificates, helpers per Definition 11
  - specs/tla/alpenglow/Certificates.tla:1
    - Stake map, thresholds (80/60/40/20), certificate constructors, validation
  - specs/tla/alpenglow/VoteStorage.tla:1
    - Pool structure, multiplicity (Definition 12), certificate storage (Definition 13), event guards (Definitions 15–16), stake queries, `GenerateCertificate`
  - specs/tla/alpenglow/VotorCore.tla:1
    - Votor state (Definition 18), Algorithm 1 handlers, Algorithm 2 helpers (`TryNotar`, `TryFinal`, `TrySkipWindow`), timeout scheduling (Definition 17)
  - specs/tla/alpenglow/Rotor.tla:1
    - Abstract Rotor constraints and relay selection
  - specs/tla/alpenglow/MC.tla; specs/tla/alpenglow/MC.cfg: model harness/constants/invariants/properties
- Constants & variables:
  - System constants: `NumValidators`, `ByzantineCount`, `GST`, `MaxSlot`, `MaxBlocks` (specs/tla/alpenglow/MainProtocol.tla:22)
  - Timing constants: `DeltaTimeout`, `DeltaBlock` (specs/tla/alpenglow/VotorCore.tla:18)
  - Window/schedule: `WindowSize`, `LeaderSchedule` (specs/tla/alpenglow/Blocks.tla:20, 26)
  - Rotor: `RotorFanout`, `RotorMinRelayStake`, `RotorGamma` (specs/tla/alpenglow/Rotor.tla:15)
  - Stake: `StakeMap` (specs/tla/alpenglow/Certificates.tla:20)
  - State variables: `validators, blocks, messages, byzantineNodes, time, finalized, blockAvailability` (specs/tla/alpenglow/MainProtocol.tla:41)
- Naming Map (whitepaper → spec):
  - Leader/slot/window → `Leader`, `FirstSlotOfWindow`, `WindowSlots` (specs/tla/alpenglow/Blocks.tla:149, 156, 175)
  - Votor state flags (ParentReady, Voted, VotedNotar, BlockNotarized, ItsOver, BadWindow) → `StateObject` on `validator.state[slot]` (specs/tla/alpenglow/VotorCore.tla:40)
  - Pool (votes, certificates, multiplicity, count-once) → `PoolState`, `CanStoreVote`, `StoreVote`, `GenerateCertificate`, `StakeFromVotes` (specs/tla/alpenglow/VoteStorage.tla:14, 36, 107, 181; specs/tla/alpenglow/Certificates.tla:64)
  - Votes (Notar/NotarFallback/Skip/SkipFallback/Final) → `VoteType` + constructors (specs/tla/alpenglow/Messages.tla:32)
  - Certificates (FastFinalization/Notarization/NotarFallback/Skip/Finalization) → `CertificateType` + constructors (specs/tla/alpenglow/Messages.tla:108)
  - Events (BlockNotarized/ParentReady/SafeToNotar/SafeToSkip) → `ShouldEmitBlockNotarized`, `ShouldEmitParentReady`, `CanEmitSafeToNotar`, `CanEmitSafeToSkip`, plus `Emit*` actions (specs/tla/alpenglow/VoteStorage.tla:250, 261, 276, 299; specs/tla/alpenglow/MainProtocol.tla:338, 382, 351, 366)
  - Timeout (Definition 17) → scheduled in `HandleParentReady`, processed in `AdvanceClock` (specs/tla/alpenglow/VotorCore.tla:251, 303)
  - Finalization (Definition 14) → `FinalizeBlock` using `HasFastFinalizationCert`, `HasNotarizationCert`, `HasFinalizationCert` (specs/tla/alpenglow/MainProtocol.tla:154; specs/tla/alpenglow/VoteStorage.tla:232)
  - Rotor/dissemination → `RotorSelect`, `RotorDisseminateSuccess`, `RotorDisseminateFailure` (specs/tla/alpenglow/Rotor.tla:31; specs/tla/alpenglow/MainProtocol.tla:242, 264)
  - Adversary assumption (Assumption 1) → `ByzantineStakeOK` invariant (specs/tla/alpenglow/MainProtocol.tla:79)

## 2. ZWD — Conformance Matrix
| Item | Whitepaper ref (quote) | Spec refs | Relation | Patch (if needed) | Severity | Evidence |
|------|-------------------------|-----------|----------|-------------------|----------|----------|
| ZWD-1 | Definition 16 (Page 22): “If s is the first slot in the leader window, the [SafeToNotar] event is emitted. Otherwise … event is emitted when Pool contains the notar-fallback certificate for the parent as well.” | `EmitSafeToNotar` additionally requires `b \in blockAvailability[v]` (specs/tla/alpenglow/MainProtocol.tla:351). Parent gating for non-first slots is already inside `CanEmitSafeToNotar` (specs/tla/alpenglow/VoteStorage.tla:276). | Narrower | Remove `b \in blockAvailability[v]` from `EmitSafeToNotar`. | Major | First-slot case does not require local block availability; fallback vote is driven by Pool stake counts and (for non-first slots) parent fallback cert. Status: Open. |
| ZWD-2 | Definition 15 (alpenglow-whitepaper.md:540–566): “ParentReady(s, hash(b)) … slot s is the first of its leader window … Pool holds a notarization or notar-fallback certificate for a previous block b, and skip certificates for every slot s′ since b.” | `ShouldEmitParentReady` matches prerequisites (specs/tla/alpenglow/VoteStorage.tla:261). `EmitParentReady` additionally enforces `p.slot + 1 = s` (specs/tla/alpenglow/MainProtocol.tla:382). | Narrower | Remove `p.slot + 1 = s` from `EmitParentReady`. | Major | Whitepaper allows b in any earlier slot if skips bridge gaps; requiring immediate predecessor is too restrictive. Status: Open. |
| ZWD-3 | Definition 12 (storing votes) (alpenglow-whitepaper.md:510–521): first notar or skip; up to 3 notar-fallback; first skip-fallback; first finalization. | `CanStoreVote` enforces caps per type (specs/tla/alpenglow/VoteStorage.tla:36). | Equivalent | — | — | Direct transcription with per-type caps. Status: Resolved. |
| ZWD-4 | Definition 11/Table 6 thresholds and “count once per slot” (alpenglow-whitepaper.md:510–554). | Threshold checks and constructors (`CanCreate*`, `Create*`, `StakeFromVotes(UniqueValidators(..))`) (specs/tla/alpenglow/Certificates.tla:64, 84). | Equivalent | — | — | Types and thresholds match table exactly. Status: Resolved. |
| ZWD-5 | Definition 14 (finalization) (alpenglow-whitepaper.md:520–566): slow path finalizes unique notarized block for slot s upon `FinalizationCert`; fast path finalizes block b upon `FastFinalizationCert`. | `FinalizeBlock` matches: fast cert OR (notarization cert for b AND finalization cert for slot) (specs/tla/alpenglow/MainProtocol.tla:154). | Equivalent | — | — | Mirrors both cases. Status: Resolved. |
| ZWD-6 | Definition 17 (timeout) (alpenglow-whitepaper.md:602–613): Timeout(i) := clock() + Δ_timeout + (i − s + 1)·Δ_block. | Timeout formula set in `HandleParentReady` (specs/tla/alpenglow/VotorCore.tla:261). | Equivalent | — | — | Matches verbatim. Status: Resolved. |
| ZWD-7 | Definition 16 (SafeToSkip) (Page 22): skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%. | `CanEmitSafeToSkip` inequality (specs/tla/alpenglow/VoteStorage.tla:299). | Equivalent | — | — | Direct transcription. Status: Resolved. |
| ZWD-8 | Rotor (§2.2): prioritise next leader, bounded fanout, require ≥γ correct relays for success. | `RotorSelect` includes next leader, caps fanout, enforces min stake; success via `EnoughCorrectRelays` (specs/tla/alpenglow/Rotor.tla:31; specs/tla/alpenglow/MainProtocol.tla:242). | Equivalent | — | — | Encodes qualitative constraints. Status: Resolved. |
| ZWD-9 | Algorithm 2 (TryNotar) (alpenglow-whitepaper.md:686–695): “or (not firstSlot and VotedNotar(hash_parent) ∈ state[s−1])”. | Non-first-slot guard uses `VotedForBlock(..parent..)`, set by prior notar vote (specs/tla/alpenglow/VotorCore.tla:111). | Equivalent | — | — | Matches pseudocode line 11. Status: Resolved. |
| ZWD-10 | Safety (Theorem 1) (alpenglow-whitepaper.md:930): finalized blocks form a single chain. | `SafetyInvariant`, `NoConflictingFinalization`, `ChainConsistency` (specs/tla/alpenglow/MainProtocol.tla:449). | Equivalent | — | — | Encodes theorem and corollary. Status: Resolved. |
| ZWD-11 | Lemma 24 (unique notarization) (alpenglow-whitepaper.md:855): at most one block notarized per slot (global). | `UniqueNotarization` checks per-node pools only (specs/tla/alpenglow/MainProtocol.tla:485). | Narrower | Add global cross-validator uniqueness covering Notarization and NotarFallback (see FCC-11). | Major | Global property missing; local-only uniqueness enforced. Status: Open. |
| ZWD-12 | Assumption 1 (<20% byz) (alpenglow-whitepaper.md:105–109): fault tolerance premise. | `ByzantineStakeOK` invariant and Init assumption (specs/tla/alpenglow/MainProtocol.tla:79, 97). | Equivalent | — | — | Models the resilience precondition. Status: Resolved. |
| ZWD-13 | Repair (§2.8): obtain missing block upon certificates. | `NeedsBlockRepair` triggers `RepairBlock` when notar or notar-fallback cert exists (specs/tla/alpenglow/MainProtocol.tla:65, 277). | Equivalent | — | — | Matches described trigger. Status: Resolved. |

## 3. CTU — TLA Pattern Audit
- SPEC form / stuttering / frame conditions:
  - Spec uses `Init /\ [][Next]_vars /\ Fairness` (specs/tla/alpenglow/MainProtocol.tla:439). Actions update relevant variables and `UNCHANGED` the rest; `vars` enumerates all state (specs/tla/alpenglow/MainProtocol.tla:41).
- Safety vs Liveness separation:
  - Safety as state predicates (`Invariant` and sub-lemmas). Liveness via `~>` under WF and GST guards (specs/tla/alpenglow/MainProtocol.tla:535). This follows guidance in tla-docs.md where fairness and liveness are treated in Sect. 3.3.
- Fairness placement:
  - WF on environment/dissemination steps (`DeliverVote`, `DeliverCertificate`, `BroadcastLocalVote`, `RotorDisseminateSuccess`, `RepairBlock`) and on `AdvanceTime`, emissions, honest propose (specs/tla/alpenglow/MainProtocol.tla:421). This models “after GST messages keep flowing” (whitepaper §2.10) and matches fairness guidance (tla-docs.md Sect. 3.3).
- Parameters / typing discipline:
  - Constants have typing assumptions; `TypeInvariant` types all variables (specs/tla/alpenglow/MainProtocol.tla:556). MC.cfg adds practical bounds. No symmetry assumptions that would bias the model.
- Vacuity / over-constraint checks:
  - Next includes adversarial actions; fairness does not force pre-GST behaviour. Liveness properties are explicitly guarded by GST. No vacuity/over-constraint issues found for the encoded claims.

Findings (CTU-#): None (Pass). Structure follows established patterns; no refactors needed.

## 4. FCC — Claim/Proof Coverage Matrix
| Claim ID | Whitepaper ref | Intended form | Spec artifact(s) | Status | Proposed property (if missing) | Notes |
|---------:|----------------|---------------|------------------|--------|--------------------------------|-------|
| FCC-1 | Theorem 1 (safety) (alpenglow-whitepaper.md:930) | Invariant: finalized blocks form a chain | `SafetyInvariant`, `NoConflictingFinalization`, `ChainConsistency` (specs/tla/alpenglow/MainProtocol.tla:449) | Covered (Resolved) | — | Encodes theorem and corollary. |
| FCC-2 | Theorem 2 (liveness) (alpenglow-whitepaper.md:1045) | Under GST and stated premises, window slots finalized by all | `EventualFinalization`, `Progress`, WF on dissemination/propose/cert (specs/tla/alpenglow/MainProtocol.tla:421, 535) | Partial (Open) | Add `WindowFinalization(s)` (see Patches). | Current liveness is generic; add per-window finalization. |
| FCC-3 | Lemma 20 (one initial vote) (alpenglow-whitepaper.md:820, 822) | Invariant | `VoteUniqueness` (specs/tla/alpenglow/MainProtocol.tla:469) | Covered (Resolved) | — | Also enforced by multiplicity limits. |
| FCC-4 | Lemma 24 (unique notarization) (alpenglow-whitepaper.md:855) | Invariant | `UniqueNotarization` (specs/tla/alpenglow/MainProtocol.tla:485) | Partial (Open) | Add `GlobalNotarizationUniqueness`. | Need cross-node uniqueness incl. NotarFallback. |
| FCC-5 | Lemma 25 (finalized implies notarized) (alpenglow-whitepaper.md:866–873) | Invariant | `FinalizedImpliesNotarized` (specs/tla/alpenglow/MainProtocol.tla:498) | Covered (Resolved) | — | Uses local pool witness. |
| FCC-6 | Definition 11/Table 6 thresholds (alpenglow-whitepaper.md:510–554) | Typing/structural | `CanCreate*`, `IsValidCertificate` (specs/tla/alpenglow/Certificates.tla:84, 191) | Covered (Resolved) | — | Encoded exactly. |
| FCC-7 | Assumption 1 (<20% byz) (alpenglow-whitepaper.md:105–109) | Assumption/state constraint | `ByzantineStakeOK` (specs/tla/alpenglow/MainProtocol.tla:79) | Covered (Resolved) | — | Safety/liveness proofs rely on it. |
| FCC-8 | Definition 17 (timeouts) (alpenglow-whitepaper.md:602–613) | State-update discipline | Timeout formula (specs/tla/alpenglow/VotorCore.tla:261) | Covered (Resolved) | — | Matches formula. |
| FCC-9 | Definition 15 (events) (alpenglow-whitepaper.md:540–554) | Event guards | `ShouldEmitBlockNotarized`, `ShouldEmitParentReady` (specs/tla/alpenglow/VoteStorage.tla:250, 261) | Covered (Resolved) | — | Matches text. |
| FCC-10 | Definition 16 (fallback events) (Page 22) | Event guards | `CanEmitSafeToNotar`, `CanEmitSafeToSkip` (specs/tla/alpenglow/VoteStorage.tla:276, 299) | Covered (Resolved) | — | Parent gating for non-first slot encoded. |
| FCC-11 | Lemma 24 (global scope) | Invariant | — | Missing (Open) | `GlobalNotarizationUniqueness` (see Patches). | Ensures cross-validator uniqueness across Notar types. |
| FCC-12 | Theorem 2 (exact form) | Liveness | — | Missing (Open) | `WindowFinalization(s)` (see Patches). | Per-window finalization under assumptions. |
| FCC-13 | “20+20 crash resilience” (Assumption 2) (alpenglow-whitepaper.md:122, 1111) | Assumption-driven claim | — | Out of scope | — | Crash-tolerance scenario not modeled in this spec. |

## 5. Patches (Minimal & Alignment-Only)
- ZWD patches:
  - No change needed for SafeToNotar; local availability aligns with Blokstor (Definition 10). 

  - ZWD-2 (Major, Open): Remove immediate-predecessor restriction in `EmitParentReady`.
    - File: specs/tla/alpenglow/MainProtocol.tla
    - Before:
      - `EmitParentReady ==`
      - `  /\ \E v \in CorrectNodes, s \in 1..MaxSlot, p \in blocks :`
      - `       /\ IsFirstSlotOfWindow(s)`
      - `       /\ p.slot + 1 = s`
      - `       /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)`
      - `       /\ ~HasState(validators[v], s, "ParentReady")`
      - `       /\ validators' = [validators EXCEPT ![v] = HandleParentReady(@, s, p.hash)]`
    - After:
      - `EmitParentReady ==`
      - `  /\ \E v \in CorrectNodes, s \in 1..MaxSlot, p \in blocks :`
      - `       /\ IsFirstSlotOfWindow(s)`
      - `       /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)`
      - `       /\ ~HasState(validators[v], s, "ParentReady")`
      - `       /\ validators' = [validators EXCEPT ![v] = HandleParentReady(@, s, p.hash)]`

- CTU refactors: None.

- FCC property additions:
  - FCC-11 (Major, Open): Global notarization uniqueness across validators and Notar types.
    - Add to specs/tla/alpenglow/MainProtocol.tla:
      - `GlobalNotarizationUniqueness ==`
      - `  \A s \in 1..MaxSlot : \A v1, v2 \in CorrectNodes :`
      - `    LET p1 == validators[v1].pool \in PoolState \* type hint`
      - `        p2 == validators[v2].pool \in PoolState`
      - `    IN \A c1 \in p1.certificates[s], c2 \in p2.certificates[s] :`
      - `         (c1.type \in {"NotarizationCert", "NotarFallbackCert"} /\`
      - `          c2.type \in {"NotarizationCert", "NotarFallbackCert"}) =>`
      - `         c1.blockHash = c2.blockHash`
    - Include `GlobalNotarizationUniqueness` in `Invariant`.

  - FCC-12 (Major, Open): Theorem 2 — per-window finalization under assumptions.
    - Add to specs/tla/alpenglow/MainProtocol.tla:
      - `NoTimeoutsBeforeGST(s) == \A v \in CorrectNodes : \A i \in (WindowSlots(s) \cap 1..MaxSlot) : validators[v].timeouts[i] = 0 \/ validators[v].timeouts[i] >= GST`
      - `WindowFinalization(s) ==`
      - `  (IsFirstSlotOfWindow(s) /\ Leader(s) \in CorrectNodes /\ NoTimeoutsBeforeGST(s) /\ time >= GST) ~>`
      - `  (\A v \in CorrectNodes : \A i \in (WindowSlots(s) \cap 1..MaxSlot) : <> (\E b \in blocks : b.slot = i /\ b.leader = Leader(s) /\ b \in finalized[v]))`
    - Optionally assert `\A s \in 1..MaxSlot : WindowFinalization(s)` in PROPERTIES when model-checking.

## 6. Open Questions & Assumptions
- Scope of Lemma 24: “notarized” is used broadly in §2.6; the proposed `GlobalNotarizationUniqueness` covers both Notarization and NotarFallback certificates across validators without altering protocol logic.
- Theorem 2 modeling: `WindowFinalization(s)` encodes the stated premises (correct window leader, no pre-GST timeouts, Rotor success after GST via WF on dissemination). It refines generic `EventualFinalization`/`Progress` to the exact whitepaper claim.
- Economics/slashing: Not normative in the provided whitepaper context; intentionally omitted from spec.

## 7. Change Log
- Pass 1: Inventory, naming map, ZWD/CTU/FCC; identified ZWD-1. Proposed minimal alignment patch.
- Pass 2: Re-verified all references; added ZWD-2 (ParentReady drift), FCC-11 (global uniqueness) and FCC-12 (window finalization) as open items with minimal patch/property snippets.
