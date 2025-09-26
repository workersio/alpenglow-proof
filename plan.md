**Goal**
- Close critical gaps with minimal, precise TLA+ additions so TLC can check all required properties using the current model entry point `specs/tla/alpenglow/MC.tla` and `MC.cfg`.

**Overview of Changes**
- Add explicit temporal properties for fast-path and recovery.
- Introduce ghost timestamps to check bounded-time claims (min(δ80%, 2δ60%)) in terms of `time`.
- Model “non-responsive” stake separately from Byzantine and add corresponding liveness.
- Keep changes localized to `MainProtocol.tla` and `MC.cfg`; adjust `MC.tla` only if needed for constants.

**1) Fast-Path Property (≥80% responsive)**
- File: `specs/tla/alpenglow/MainProtocol.tla`
- Add CONSTANTS
  - `Bound80Steps \in Nat \ {0}` (abstract time bound for fast path, measured in increments of `time`).
- Add ghost state (VARIABLES)
  - `fastTrigger`: `[Slots -> Nat]` initialized to 0; records first `time` when a slot becomes fast-finalizable.
- Update actions to set ghost timestamps
  - In `GenerateCertificateAction(v, slot)`: when `CanCreateFastFinalizationCert(GetVotesForSlot(validators[v].pool, slot), slot, block)` holds for any block in `slot` and `fastTrigger[slot] = 0`, set `fastTrigger'[slot] = time` (or `time'` if using `AdvanceTime` clocking; use current `time`).
- Add properties
  - `FastPathLeadsToFinalize`: after GST, if `fastTrigger[s] > 0`, eventually some validator finalizes a block in slot `s`.
    - `(time >= GST) ~> (\A s \in 1..MaxSlot : fastTrigger[s] > 0 => <>(\E v \in Validators, b \in blocks : b.slot = s /\ b \in finalized[v]))`
  - `BoundedFastFinalization`: if `fastTrigger[s] > 0`, then eventual finalization of slot `s` occurs in a state where `time <= fastTrigger[s] + Bound80Steps`.
    - `\A s \in 1..MaxSlot : fastTrigger[s] > 0 => <>( (\E v,b : b.slot = s /\ b \in finalized[v]) /\ time <= fastTrigger[s] + Bound80Steps )`
- Add both to `MC.cfg` PROPERTIES.

**2) Slow-Path Liveness with ≥60% responsive**
- File: `specs/tla/alpenglow/MainProtocol.tla`
- Add CONSTANTS
  - `Bound60Steps \in Nat \ {0}` (abstract time bound from trigger to slow finalization).
- Add ghost state (VARIABLES)
  - `slowTrigger`: `[Slots -> Nat]` initialized to 0; records first `time` when a slot is slow-finalizable (i.e., FinalizationCert is creatable on 60% path).
- Update actions to set ghost timestamps
  - In `GenerateCertificateAction(v, slot)`: when `CanCreateFinalizationCert(GetVotesForSlot(validators[v].pool, slot), slot)` holds and `slowTrigger[slot] = 0`, set `slowTrigger'[slot] = time`.
- Add properties
  - `Liveness60Responsive`: after GST, with stake assumptions (see §3), progress holds (reuse `Progress`): `(time >= GST /\ ByzantineStakeOK /\ UnresponsiveStakeOK) ~> Progress`.
  - `BoundedSlowFinalization`: `\A s : slowTrigger[s] > 0 => <>( (\E v,b : b.slot = s /\ b \in finalized[v]) /\ time <= slowTrigger[s] + Bound60Steps )`.
- Add both to `MC.cfg` PROPERTIES.

**3) Model Non-Responsive Stake (≤20%) and Recovery**
- File: `specs/tla/alpenglow/MainProtocol.tla`
- Add CONSTANTS
  - `UnresponsiveCount \in Nat` (small in MC model; default 0 in `MC.cfg`).
- Add VARIABLES
  - `unresponsiveNodes`: subset of `Validators` (chosen in `Init`) of cardinality `UnresponsiveCount`, disjoint from `byzantineNodes`.
- Update macros and assumptions
  - Redefine `CorrectNodes == Validators \ (byzantineNodes \cup unresponsiveNodes)`.
  - Add `UnresponsiveStakeOK == CalculateStake(unresponsiveNodes) * 100 <= TotalStake * 20` and include in `Init` and in `Invariant`.
- Properties
  - `RecoveryAfterGST`: From any history, once `time >= GST`, new finalization occurs eventually. This can alias `BasicLiveness` or restate it to emphasize recovery.
    - Use existing `BasicLiveness` or add `RecoveryAfterGST == BasicLiveness` and list in `MC.cfg` PROPERTIES.

**4) Optional: Dissemination Timestamp (if you want tighter mapping to δ)**
- File: `specs/tla/alpenglow/MainProtocol.tla`
- Add ghost state
  - `disseminatedAt`: `[Slots -> Nat]` initialized to 0.
- Update dissemination actions
  - In `RotorDisseminateSuccess(b)`: set `disseminatedAt'[b.slot] = IF disseminatedAt[b.slot] = 0 THEN time ELSE disseminatedAt[b.slot]`.
- (Optional) Strengthen bounded properties to use `disseminatedAt[s]` as the reference time instead of first creatable condition.

**5) MC Configuration**
- File: `specs/tla/alpenglow/MC.cfg`
- Add to CONSTANTS block suitable small values for quick TLC:
  - `Bound80Steps = 2`
  - `Bound60Steps = 4`
  - `UnresponsiveCount = 0` (or 1 for scenarios)
- Add to PROPERTIES block:
  - `FastPathLeadsToFinalize`
  - `BoundedFastFinalization`
  - `Liveness60Responsive`
  - `BoundedSlowFinalization`
  - `RecoveryAfterGST`

**6) Testing Instructions**
- Run model checking (from repo root):
  - `java -jar tla2tools.jar -tool -config specs/tla/alpenglow/MC.cfg specs/tla/alpenglow/MC.tla`
- Iterate with small `MaxSlot/MaxBlocks` (already set) and adjust `Bound80Steps/Bound60Steps` if needed to accommodate fairness scheduling under GST.

**Design Notes**
- Ghost variables (`fastTrigger`, `slowTrigger`, `disseminatedAt`) do not affect protocol semantics and are only assigned monotonically to support bounded-time assertions.
- Using `GenerateCertificateAction` as the observation point keeps the implementation localized and reuses existing vote aggregation logic (best practice: observe preconditions where they are computed).
- Redefining `CorrectNodes` to exclude `unresponsiveNodes` integrates seamlessly with existing fairness guards that already quantify over `CorrectNodes`.

**Out-of-Scope (Intentionally Not Changed)**
- Rotor internals, certificate definitions, and Votor algorithms remain unchanged; we only add observation/timestamps and properties.

