# Audit: EmitBlockNotarized

## 1. Code Under Audit

```tla
EmitBlockNotarized ==
    /\ \E v \in CorrectNodes, b \in blocks :
         /\ b.slot \in 1..MaxSlot
         /\ ShouldEmitBlockNotarized(validators[v].pool, b.slot, b.hash)
         /\ ~HasState(validators[v], b.slot, "BlockNotarized")
         /\ validators' = [validators EXCEPT ![v] =
                               HandleBlockNotarized(@, b.slot, b.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>
```

Defined in: `specs/tla/alpenglow/MainProtocol.tla`

References:
- `ShouldEmitBlockNotarized(pool, slot, blockHash)` → `specs/tla/alpenglow/VoteStorage.tla`
- `HasState(validator, slot, stateObj)` → `specs/tla/alpenglow/VotorCore.tla`
- `HandleBlockNotarized(validator, slot, blockHash)` → `specs/tla/alpenglow/VotorCore.tla`
- `CorrectNodes`, `validators`, `blocks`, `messages`, `byzantineNodes`, `time`, `finalized`, `blockAvailability`, `MaxSlot` → `specs/tla/alpenglow/MainProtocol.tla`


## 2. Whitepaper Sections / References

- Definition 15 (Pool events): Page 21 — “BlockNotarized(slot(b), hash(b)): Pool holds a notarization certificate for block b.”
- Algorithm 1 (Votor event loop): Page 24, lines 9–11 — on BlockNotarized: add BlockNotarized to state and then TRYFINAL.
- Definition 13 (certificates): Pages 20–21 — certificate creation/storage rules that make ShouldEmitBlockNotarized true.
- Definition 14 (finalization): Pages 21–22 — TRYFINAL triggers finalization voting when possible.


## 3. Reasoning and Conformance

- Event trigger (Pool condition):
  - The guard `ShouldEmitBlockNotarized(validators[v].pool, b.slot, b.hash)` reduces to `HasNotarizationCert(pool, slot, blockHash)` (VoteStorage). This exactly matches Definition 15: emit BlockNotarized when Pool holds a notarization certificate for block b.

- Single‑emission per slot:
  - The guard `~HasState(validators[v], b.slot, "BlockNotarized")` prevents re‑emission, matching the one‑time transition semantics in Algorithm 1 (line 9). Once the flag is set, the event is no longer enabled for that `(v, slot)`.

- State update and immediate follow‑up:
  - The next‑state update calls `HandleBlockNotarized(@, b.slot, b.hash)` (VotorCore), which:
    - Adds `BlockNotarized` to the validator’s state for the slot, and
    - Invokes `TryFinal(slot, hash)` to attempt a finalization vote (Algorithm 2, TRYFINAL) — this is exactly Algorithm 1 lines 10–11.
  - Messages remain unchanged in this step, which is consistent with the spec’s pattern: votes are stored locally first, and `BroadcastLocalVote` later publishes them to the network (MainProtocol). This separation matches the whitepaper’s “broadcast newly added” in Definition 13 while keeping the event atomic.

- Typing/bounds:
  - `b.slot \in 1..MaxSlot` ensures we don’t model genesis (slot 0) for notarization events, consistent with Init using genesis only for initial ParentReady. All other variables are UNCHANGED, consistent with the event’s scope.

- Fairness:
  - `EmitBlockNotarized` is included under weak fairness in `MainProtocol` so that if the guard persists, TLC considers it eventually firing, reflecting the whitepaper’s eventual progress after GST.


## 4. Conclusion

The `EmitBlockNotarized` action conforms to the whitepaper’s Definition 15 and the control‑flow in Algorithm 1 (lines 9–11). It emits the event precisely when the Pool holds a notarization certificate for a block, sets the correct state flag only once, and immediately triggers the attempt to cast a finalization vote via `TRYFINAL`. The handling of messages is consistent with the spec’s design where local vote storage precedes broadcast via a separate action. Overall, this TLA+ action correctly models the intended abstraction.


## 5. Open Questions / Concerns

- Dependency on `b \in blocks`:
  - The guard quantifies `b \in blocks`. Since notarization votes (and thus certificates) are created only after seeing a concrete block object (TryNotar takes a `block` record), a notarization certificate should not exist for a non‑existent block. Therefore this constraint is sound. It is also slightly stronger than the minimal whitepaper condition (which only needs block hash and slot), but does not appear to exclude legitimate behaviors in this model.

- Slot domain `1..MaxSlot` vs `Slots`:
  - The use of `1..MaxSlot` is consistent with bounded model checking and the genesis handling strategy. If `Slots` ever deviates (e.g., non‑contiguous sets in custom harnesses), consider aligning guards to `Slots \cap 1..MaxSlot` for robustness across harnesses.

- Final vote broadcast timing:
  - `TryFinal` stores the final vote locally and relies on `BroadcastLocalVote` fairness to publish it. This matches the spec’s event decomposition, but it is worth keeping this coupling in mind for liveness proofs (the spec already includes fairness for `BroadcastLocalVote`).


## 6. Suggestions for Improvement

- Strengthen a derived invariant:
  - Add a check that whenever `BlockNotarized` is present in a validator’s state for slot `s` and hash `h`, the Pool indeed holds a matching notarization certificate: e.g.,
    - `\A v \in CorrectNodes, s \in 1..MaxSlot : ("BlockNotarized" \in validators[v].state[s]) => (\E b \in blocks : b.slot = s /\ HasNotarizationCert(validators[v].pool, s, b.hash))`.
    - This is already implied by construction but helps catch unintended alternative transitions.

- Optional guard clarity:
  - Document (in comments) why `messages` remain UNCHANGED here (votes broadcasted via `BroadcastLocalVote`). This aids readers correlating Algorithm 1’s “broadcast” lines with the model’s event splitting.

- Harness consistency:
  - If using non‑standard `Slots`, consider replacing `b.slot \in 1..MaxSlot` with `b.slot \in (Slots \cap 1..MaxSlot)` to avoid accidental guard disablement in custom runs.

