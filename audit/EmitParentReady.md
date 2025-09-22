# Audit: EmitParentReady

## 1. Code Under Audit

```tla
EmitParentReady ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, p \in blocks :
         /\ IsFirstSlotOfWindow(s)
         /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)
         /\ ~HasState(validators[v], s, "ParentReady")
         /\ validators' = [validators EXCEPT ![v] = HandleParentReady(@, s, p.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>
```

Defined in: `specs/tla/alpenglow/MainProtocol.tla:381`

References (definitions and handlers):
- `IsFirstSlotOfWindow(slot)` → `specs/tla/alpenglow/Blocks.tla:161`
- `ShouldEmitParentReady(pool, slot, parentHash, parentSlot)` → `specs/tla/alpenglow/VoteStorage.tla:261`
- `HasState(validator, slot, stateObj)` → `specs/tla/alpenglow/VotorCore.tla:79`
- `HandleParentReady(validator, slot, parentHash)` → `specs/tla/alpenglow/VotorCore.tla:251`
- `WindowSlots(slot)` (used by `HandleParentReady`) → `specs/tla/alpenglow/Blocks.tla:175`
- Certificate queries used by `ShouldEmitParentReady`: `HasNotarizationCert`, `HasNotarFallbackCert`, `HasSkipCert` → `specs/tla/alpenglow/VoteStorage.tla:214, 220, 226`
- State and sets: `CorrectNodes`, `validators`, `blocks`, `messages`, `byzantineNodes`, `time`, `finalized`, `blockAvailability`, `MaxSlot` → `specs/tla/alpenglow/MainProtocol.tla:22–50`


## 2. Whitepaper Sections / References

- Definition 15 (Pool events): `alpenglow-whitepaper.md:543–547`
  - ParentReady(s, hash(b)) conditions: first slot of window, Pool has notarization or notar-fallback certificate for previous block b, and skip certificates for all slots since b: slot(b) < s' < s.
- Definition 17 (Timeouts): `alpenglow-whitepaper.md:607–613`
  - On first ParentReady(s, …), schedule Timeout(i) for all i in WINDOW_SLOTS(s): clock() + Δ_timeout + (i − s + 1)·Δ_block.
- Algorithm 1 (Votor event loop): `alpenglow-whitepaper.md:651–655`
  - Upon ParentReady(s, hash(b)): add ParentReady(hash(b)) to state, CHECKPENDINGBLOCKS(), SETTIMEOUTS(s).
- Algorithm 2 helpers (TRYNOTAR/TRYSKIPWINDOW, used indirectly by handler): `alpenglow-whitepaper.md:685–715`
- Section 2.5 Pool (vote/cert storage rules) and Table 6 thresholds: `alpenglow-whitepaper.md:509–534`, `alpenglow-whitepaper.md:499–506`
- Section 2.7 Block Creation (semantics around ParentReady and parent selection): `alpenglow-whitepaper.md:721–731`


## 3. Reasoning and Conformance

- Guard matches Definition 15 exactly.
  - `ShouldEmitParentReady(pool, s, parentHash, parentSlot)` encodes:
    - `IsFirstSlotOfWindow(s)`; AND
    - Pool has notarization OR notar-fallback cert for block at `parentSlot` with `parentHash`; AND
    - Pool has skip certificates for all gaps `(parentSlot+1)..(s-1)`.
  - See `specs/tla/alpenglow/VoteStorage.tla:261–266`. This mirrors `alpenglow-whitepaper.md:546` verbatim.
  - The action also checks `IsFirstSlotOfWindow(s)` redundantly; harmless and self-documenting.

- Single emission per validator and slot.
  - `~HasState(validators[v], s, "ParentReady")` prevents re-emitting ParentReady for the same `(v, s)`, consistent with the one-time state transition in Algorithm 1.

- State update handler aligns with Algorithm 1 and Definition 17.
  - `HandleParentReady`:
    - Adds `ParentReady` to the state for slot `s` and records `parentReady[s] = parentHash` (`specs/tla/alpenglow/VotorCore.tla:251–254`), matching Algorithm 1 line 13.
    - Schedules timeouts for all slots in the leader window starting at `s` using `clock + Δ_timeout + (i − s + 1)·Δ_block` (`:261–263`), matching Definition 17 (`alpenglow-whitepaper.md:607–613`).
    - Calls `CheckPendingBlocks` to run `TRYNOTAR` on any stored pending blocks (`:264`), corresponding to Algorithm 1 line 14.
  - Note: The handler sets timeouts before checking pending blocks (lines 255–264) whereas Algorithm 1 lists CHECKPENDINGBLOCKS before SETTIMEOUTS. These operations are independent; the ordering does not affect safety or liveness because timeout scheduling depends only on `(clock, s)` and window indices, not on pending-block outcomes. The model still preserves the whitepaper semantics.

- Choice of `p ∈ blocks` and parent identification.
  - The action quantifies `p ∈ blocks` and passes `p.hash`/`p.slot` to the guard and handler. This is consistent with how certificates are generated (only for concrete blocks introduced by propose actions). It ties the ParentReady marker to an actual block object, aligning with Section 2.7’s requirement that the leader builds on some parent `b_p` for which ParentReady was emitted.

- Fairness and progress.
  - `EmitParentReady` is included under weak fairness (`specs/tla/alpenglow/MainProtocol.tla:427`), ensuring that once the guard persists (e.g., after GST and when certificates are present), the event eventually fires, matching the whitepaper’s eventual progress assumptions.


## 4. Conclusion

`EmitParentReady` correctly models the ParentReady event from Definition 15. The guard conditions match the whitepaper exactly (first slot, notar/notar-fallback on the previous block, skip certs for any gaps). The handler updates state, records the parent hash, schedules timeouts according to Definition 17, and rechecks pending blocks as per Algorithm 1. The redundant first-slot check is benign. No deviations were found that would change the abstract behavior relative to the whitepaper.


## 5. Open Questions / Concerns

- Ordering of SETTIMEOUTS vs CHECKPENDINGBLOCKS.
  - The spec schedules timeouts before checking pending blocks, while Algorithm 1 lists the reverse order. These are functionally independent, but for line-by-line traceability to Algorithm 1 you could swap the order in `HandleParentReady` (cosmetic, not correctness-affecting).

- Redundant guard.
  - `IsFirstSlotOfWindow(s)` appears in both the action and inside `ShouldEmitParentReady`. The duplication is harmless but could be removed from the action to avoid confusion.

- Quantification over `p ∈ blocks`.
  - Definition 15 only requires the presence of certificates, not the local availability of the block object. In this model, certificates arise only from votes on existing `blocks`, so `p ∈ blocks` is consistent. If the model were extended to admit certificates for unknown blocks (e.g., via out-of-band injection), the extra `p ∈ blocks` qualifier would suppress ParentReady; this scenario is out of scope here but worth documenting as a modeling assumption.


## 6. Suggestions for Improvement

- Align handler step order with Algorithm 1 for readability:
  - In `HandleParentReady`, call `CheckPendingBlocks` before `SetTimeouts`. This makes the code path match `alpenglow-whitepaper.md:651–655` line-by-line, aiding audits without changing semantics.

- Remove redundant first-slot check in the action:
  - Keep `IsFirstSlotOfWindow` only inside `ShouldEmitParentReady` to reduce duplication. The guard remains equivalent.

- Optional invariant to bind state to Pool evidence:
  - Add a cross-check invariant tying `ParentReady` state to Pool evidence, e.g.: for all correct `v` and `s`, if `ParentReady ∈ validators[v].state[s]` then there exists a `p` and `parentSlot` such that `HasNotarizationCert ∨ HasNotarFallbackCert` holds at `parentSlot` for `p.hash` and `HasSkipCert` holds for all gaps. This is already implied by the transition but helps detect unintended alternative transitions in future edits.

- Comment on modeling assumption:
  - Note in `MainProtocol.tla` near `EmitParentReady` that the model assumes certificates refer to `p ∈ blocks` (consistent with how votes and certs are created), clarifying why `p` is quantified from `blocks`.

