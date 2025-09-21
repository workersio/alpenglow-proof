**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:119`

```
ProcessTimeout(v, slot) ==
    /\ v \in CorrectNodes
    /\ slot \in Slots
    /\ slot <= MaxSlot
    /\ validators[v].timeouts[slot] > 0
    /\ time >= validators[v].timeouts[slot]
    /\ ~HasState(validators[v], slot, "Voted")
    /\ validators' = [validators EXCEPT ![v] = HandleTimeout(validators[v], slot)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>
```

**Whitepaper References**

- Algorithm 1 — Timeout handling and skip window
  - Heading: `alpenglow-whitepaper.md:634`
  - Line 6 trigger and guard: `alpenglow-whitepaper.md:643`
  - Line 8 TRYSKIPWINDOW(s): `alpenglow-whitepaper.md:645`
- Definition 17 — Timeout scheduling (absolute times)
  - Definition: `alpenglow-whitepaper.md:607`
  - Formula placement context: `alpenglow-whitepaper.md:613`
- Algorithm 2 — TRYSKIPWINDOW details (skip unvoted slots)
  - Function header (lines 22–27): `alpenglow-whitepaper.md:705`
- Definition 18 — Votor state objects (Voted, BadWindow, ItsOver, VotedNotar)
  - State list: `alpenglow-whitepaper.md:615` and `alpenglow-whitepaper.md:630`

Related spec context used by this action:

- Timeout scheduling on ParentReady (Def. 17): `specs/tla/alpenglow/VotorCore.tla:251`
  - SetTimeouts formula: `specs/tla/alpenglow/VotorCore.tla:257`
- Timeout handler used by this action: `specs/tla/alpenglow/VotorCore.tla:229`
- TRYSKIPWINDOW implementation (Alg. 2, 22–27): `specs/tla/alpenglow/VotorCore.tla:161`
- Timeout processing on clock tick: `specs/tla/alpenglow/VotorCore.tla:303`
- Global time tick linking time→clock: `specs/tla/alpenglow/MainProtocol.tla:228`
- Sets and types (`Validators`, `Slots`): `specs/tla/alpenglow/Messages.tla:12`

**Reasoning**

- Guards match Algorithm 1 lines 6–8.
  - The precondition `validators[v].timeouts[slot] > 0 /\ time >= validators[v].timeouts[slot]` models “upon Timeout(s)” by recognizing the scheduled time has arrived (Definition 17). The additional `~HasState(..., "Voted")` matches the guard in Algorithm 1 line 7 — only skip if we have not already cast an initial vote in slot s.
  - Restricting to `v \in CorrectNodes` is consistent with the model’s design: Byzantine behavior is modeled by `ByzantineAction`, while honest timeout processing follows the algorithm.

- State update matches the algorithm’s body.
  - The transition delegates to `HandleTimeout(validators[v], slot)` which sets `timeouts[slot] := 0` (one-shot behavior) and, if still not `Voted`, calls `TrySkipWindow` to cast skip votes for all unvoted slots in the leader window. This directly embodies Algorithm 1 line 8 and Algorithm 2 lines 22–27.
  - `TrySkipWindow` adds `Voted` and `BadWindow` flags and stores a `SkipVote` for each still-unvoted slot in the window, also clearing pending blocks for those slots. This matches the whitepaper’s semantics precisely.

- Time model aligns with Definition 17.
  - Timeouts are scheduled in `HandleParentReady` as `clock + Δ_timeout + (i - s + 1)·Δ_block` (VotorCore SetTimeouts), exactly as in Definition 17. `AdvanceTime` increments the global `time` and updates each correct validator’s `clock` to `time'`, ensuring local `clock()` equals the model’s `time` for correct nodes.
  - `ProcessTimeout` tests against the global `time`, which is the model’s abstraction of `clock()` in the whitepaper. This keeps the schedule coherent with the earlier SetTimeouts computation, which used the then-current `clock` (equal to the global `time` at scheduling in this model).

- Idempotence and non-duplication.
  - Even though expired timeouts are also processed by `AdvanceClock` during `AdvanceTime`, `HandleTimeout` zeroes the per-slot timeout and `TrySkipWindow` sets `Voted`, preventing repeated skip votes. Vote multiplicity limits (Definition 12) in `VoteStorage` further ensure storage of only one `SkipVote` per validator/slot.

- Scope of state changes is correct.
  - Consistent with Algorithm 1, this action only mutates the local validator state; `blocks`, `messages`, `time`, `finalized`, and `blockAvailability` remain unchanged here. Broadcasting of local votes happens separately through the network actions in `MainProtocol`.

**Conclusion**

- `ProcessTimeout` correctly implements the whitepaper’s timeout-triggered skip behavior:
  - It fires only when the scheduled timeout elapses and no initial vote exists for the slot, per Algorithm 1.
  - It triggers `TrySkipWindow` as required, which casts skip votes for all unvoted slots in the window (Algorithm 2).
  - Timeout scheduling (Definition 17) and the time/clock relation are faithfully modeled, ensuring the guard reflects actual timeout expiry.
  - Safety is preserved: multiplicity and state flags prevent double initial votes; liveness is aided by ensuring unvoted slots are skipped so the protocol progresses.

**Open Questions / Concerns**

- Redundancy with `AdvanceTime`.
  - The model processes expired timeouts in two ways: explicitly via `ProcessTimeout` and implicitly via `AdvanceTime` → `AdvanceClock`. This is safe (idempotence holds) but potentially redundant. It may slightly expand the state space explored by the model checker.

- Guard strength vs. Algorithm 1 minimalism.
  - The whitepaper’s Timeout handler only checks `Voted ∉ state[s]`. Here, the additional guards (`timeouts[s] > 0`, `time >= timeouts[s]`) model “scheduled timeout” explicitly. This is appropriate for TLA+, but readers should note the difference in presentation.

- Fairness.
  - There is no explicit fairness on `ProcessTimeout` in `Fairness`; progress relies on `AdvanceTime` fairness to eventually process timeouts anyway. This is fine, but worth noting as the reason we don’t need explicit fairness on this action.

**Suggestions for Improvement**

- Simplify: Consider removing `ProcessTimeout` from `Next` and relying solely on `AdvanceTime` to process timeouts. This reduces transition redundancy while preserving behavior, since `AdvanceClock` calls `HandleTimeout` for all expired timers.
- Document time model: Add a brief comment near `ProcessTimeout` noting that `time` represents the `clock()` used in Definition 17, and that `HandleParentReady` schedules timeouts against the same absolute time base.
- Optional guard: If desired, add `ItsOver` as an early check in `HandleTimeout` (though currently harmless due to `Voted` covering initial-vote uniqueness and `ItsOver` being checked in fallback handlers).

