# Audit: AdvanceClock (VotorCore)

1. Code that you are auditing.

```tla
AdvanceClock(validator, newTime) ==
    LET expiredTimeouts == {s \in Slots : 
                            validator.timeouts[s] > 0 /\ 
                            validator.timeouts[s] <= newTime}
        RECURSIVE ProcessTimeouts(_,_)
        ProcessTimeouts(val, slots) ==
            IF slots = {} THEN val
            ELSE
                LET s == CHOOSE x \in slots : TRUE
                    newVal == HandleTimeout(val, s)
                IN ProcessTimeouts(newVal, slots \ {s})
    IN [ProcessTimeouts(validator, expiredTimeouts) EXCEPT !.clock = newTime]
```

References in repo:
- Definition location: `specs/tla/alpenglow/VotorCore.tla:307`
- Uses: `specs/tla/alpenglow/MainProtocol.tla:407` (via `AdvanceTime`)
- Called helper: `HandleTimeout` at `specs/tla/alpenglow/VotorCore.tla:231`
- Timeout scheduling site: `HandleParentReady` at `specs/tla/alpenglow/VotorCore.tla:255` (uses `WindowSlots`)
- Window computation: `specs/tla/alpenglow/Blocks.tla:211` (`WindowSlots`), first-of-window: `:201`, `:205`
- Slots type/assumptions: `specs/tla/alpenglow/Messages.tla:18`, `:25–:26`

2. The whitepaper section and references that the code represents.

- Local clocks and no need for synchronization: `alpenglow-whitepaper.md:224` (Timeout, §1.5)
- Definition 17 (Timeout scheduling): `:607`, formula `:609`, note `:613` (never in past)
- Algorithm 1 (Timeout handler): `:643–:646`
- Algorithm 2 (SETTIMEOUTS loop): `:681–:685`

3. The reasoning behind the code and what the whitepaper claims.

- Paper intent (Def. 17 + Alg. 1/2): When ParentReady(s, …) fires for the first slot s of a leader window, a node schedules Timeout(i) for every i ∈ WINDOWSLOTS(s) at time
  clock() + Δ_timeout + (i − s + 1) · Δ_block, then, upon Timeout(i), if the node hasn’t voted in slot i, it triggers TRYSKIPWINDOW(i).
- Scheduling (matches Def. 17): The spec sets timeouts in `HandleParentReady` as
  `timeouts[i] := val.clock + DeltaTimeout + ((i - s + 1) * DeltaBlock)` for all i ∈ WindowSlots(s) (see `specs/tla/alpenglow/VotorCore.tla:259–:268`). Assumptions `DeltaTimeout, DeltaBlock ∈ Nat \ {0}` ensure future deadlines; `IsFirstSlotOfWindow(s)` precondition (via `ShouldEmitParentReady`) ensures (i − s + 1) ≥ 1 (whitepaper `:613`).
- Emitting Timeout events: `AdvanceClock` implements the emission step. For a requested `newTime`, it collects all slots whose scheduled timeout is nonzero and ≤ `newTime` (matured deadlines) and iteratively calls `HandleTimeout(val, s)` on each. Finally, it writes back the local clock as `newTime`.
- Timeout handler semantics (Alg. 1 lines 6–8): `HandleTimeout` clears the one-shot timer and, if the node hasn’t voted in the slot and isn’t already done (`ItsOver`), it calls `TrySkipWindow` to broadcast skip votes for all unvoted slots in that window (see `specs/tla/alpenglow/VotorCore.tla:231–:268`). This matches “upon Timeout(s) do … TRYSKIPWINDOW(s).”
- Order/idempotence: `ProcessTimeouts` chooses an arbitrary order (`CHOOSE`). Because `TrySkipWindow` marks all unvoted slots in the window as Voted/BadWindow, subsequent timeouts for the same window become no-ops (they just clear their timer). Therefore, behavior is order-independent and aligns with the paper’s single-threaded event loop.
- Global→local time modeling: The system action `AdvanceTime` increments a single model `time` and applies `AdvanceClock(v, time')` to each correct validator (see `specs/tla/alpenglow/MainProtocol.tla:399–:411`). This is a modeling convenience; it preserves the paper’s “local clocks only” semantics while enabling uniform checking of Def. 17 deadlines.
- Safety invariant tie-in: `TimeoutsInFuture` (never schedule in the past) is stated as a global invariant (`specs/tla/alpenglow/MainProtocol.tla:908`) and is preserved by (i) Def. 17’s formula and (ii) the fact that `AdvanceClock` processes all matured deadlines and advances `validator.clock := newTime`.

4. The conclusion of the audit.

- Verdict: Matches whitepaper. `AdvanceClock` correctly realizes the Timeout event emission that follows Def. 17 scheduling, and its interaction with `HandleTimeout` implements Algorithm 1 lines 6–8 faithfully. The model’s global-time driver is explicitly documented and consistent with §1.5’s “local clocks” stance. Invariants (e.g., `TimeoutsInFuture`) support correctness claims in the spec.

5. Any open questions or concerns.

- Finite processing set: The recursive `ProcessTimeouts` removes one slot per iteration; its well-foundedness relies on the set of matured timeouts being finite at each step. In practice this holds because timeouts are scheduled only for finite windows and cleared on expiry, and in MC we bound `Slots`. For completeness, one could document this finiteness assumption explicitly.
- Monotonic clock precondition: The function does not guard `newTime ≥ validator.clock`; correctness relies on the caller (`AdvanceTime`) ensuring monotonic time. This is satisfied in the spec but could be asserted as an invariant for clarity.

6. Any suggestions for improvement.

- Add a small invariant documenting local clock monotonicity, e.g., `\A v: validators[v].clock' ≥ validators[v].clock` across `Next`, or a comment at `AdvanceClock` noting the expectation `newTime ≥ validator.clock`.
- Optional determinism for model-checking: If desired, replace `CHOOSE x ∈ slots` with a selection of the minimum slot to make runs more reproducible. Behavior is equivalent.
- Scope restriction (MC-only): Define `expiredTimeouts == {s ∈ 1..MaxSlot : …}` in a bounded configuration to avoid quantifying over an unbounded `Slots` when running larger models; not required for correctness, just performance/clarity.

```text
Overall: PASS (semantics aligned with Def. 17; no material deviations)
```

