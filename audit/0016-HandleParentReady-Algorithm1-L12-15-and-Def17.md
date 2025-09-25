# Audit: HandleParentReady — Algorithm 1 (lines 12–15) and Definition 17

## 1. Code Audited

```tla
HandleParentReady(validator, slot, parentHash) ==
    LET newValidator == AddState(validator, slot, "ParentReady")
        withParent == [newValidator EXCEPT !.parentReady[slot] = parentHash]
        afterCheck == CheckPendingBlocks(withParent)
        windowSlots == WindowSlots(slot)
        \* Set timeouts for all slots in window
        RECURSIVE SetTimeouts(_,_)
        SetTimeouts(val, slots) ==
            IF slots = {} THEN val
            ELSE
                LET s == CHOOSE x \in slots : TRUE
                    timeout == val.clock + DeltaTimeout + ((s - slot + 1) * DeltaBlock)
                IN SetTimeouts([val EXCEPT !.timeouts[s] = timeout], slots \ {s})
    IN SetTimeouts(afterCheck, windowSlots \cap Slots)
```

- Definition location: `specs/tla/alpenglow/VotorCore.tla:255`
- Invocation site: `specs/tla/alpenglow/MainProtocol.tla:675`

## 2. Whitepaper Sections and References

- Definition 15 (Pool events) — ParentReady:
  - `alpenglow-whitepaper.md:543`, `alpenglow-whitepaper.md:546`
- Algorithm 1 (Votor event loop) — ParentReady handler (lines 12–15):
  - `alpenglow-whitepaper.md:651`
- Definition 17 (Timeouts) — schedule and formula:
  - Header: `alpenglow-whitepaper.md:607`
  - Formula: `alpenglow-whitepaper.md:609`
  - Note “ParentReady only for first slot; (i − s + 1) ≥ 1”: `alpenglow-whitepaper.md:613`
- Definition 18 (Votor state) — includes ParentReady(hash(b)) as a state object:
  - `alpenglow-whitepaper.md:615`

## 3. Reasoning: Code vs. Whitepaper Claims

- State update (Algorithm 1, line 13; Definition 18):
  - The code adds the state marker `"ParentReady"` to `state[slot]` and stores the associated parent hash in `parentReady[slot]`.
  - This matches Definition 18, which models `ParentReady(hash(b))` as a per-slot state item. The spec splits the boolean marker and the carried hash into `state` and `parentReady` respectively, a consistent pattern used elsewhere (e.g., `VotedNotar` is tracked via votes rather than embedding the hash in the state set).

- Pending blocks re-check (Algorithm 1, line 14):
  - `CheckPendingBlocks` is called immediately after recording ParentReady, enabling immediate re-attempts to notarize any stored blocks whose preconditions now hold (notably, first-slot gating on ParentReady in `TryNotar`).
  - This follows Algorithm 1, which triggers `CHECKPENDINGBLOCKS()` after ParentReady.

- Timeout scheduling (Algorithm 1, line 15; Definition 17):
  - The function computes `windowSlots == WindowSlots(slot)` and sets `timeouts[i]` for every slot i in the window using:
    - `val.clock + DeltaTimeout + ((i - slot + 1) * DeltaBlock)`
  - This implements Definition 17’s schedule exactly:
    - Timeout(i): `clock() + Δ_timeout + (i - s + 1) · Δ_block`, where s is the first slot of the window.
  - The invocation site `EmitParentReady` enforces `IsFirstSlotOfWindow(slot)` via `ShouldEmitParentReady(...)` (see `specs/tla/alpenglow/VoteStorage.tla:268`), ensuring `slot` is the first window slot, so `(i - slot + 1) ≥ 1` as required by the whitepaper note.

- Event wiring and single emission:
  - ParentReady emission is guarded by `~HasState(validators[v], s, "ParentReady")` at the call site (`specs/tla/alpenglow/MainProtocol.tla:675`), matching Definition 17’s “first event ParentReady(s,…)” requirement for starting timers.
  - Scheduled timeouts feed into `AdvanceClock`/`HandleTimeout` (`specs/tla/alpenglow/VotorCore.tla:307`) consistent with Algorithm 1 lines 6–8.

## 4. Cross-Module References (complete context)

- Local helpers/state:
  - `AddState`, `CheckPendingBlocks`, `ValidatorState.clock`, `ValidatorState.timeouts` — `specs/tla/alpenglow/VotorCore.tla`
- Window arithmetic:
  - `WindowSlots`, `IsFirstSlotOfWindow` — `specs/tla/alpenglow/Blocks.tla:211`
- Emission guard for ParentReady:
  - `ShouldEmitParentReady` — `specs/tla/alpenglow/VoteStorage.tla:268`
  - Emitter `EmitParentReady` — `specs/tla/alpenglow/MainProtocol.tla:675`
- Constants and domains:
  - `DeltaTimeout`, `DeltaBlock` — `specs/tla/alpenglow/VotorCore.tla`
  - `Slots` — `specs/tla/alpenglow/Messages.tla:19`

## 5. Conclusion

- The implementation of `HandleParentReady` faithfully mirrors Algorithm 1 (lines 12–15): it records ParentReady, re-checks pending blocks, and schedules timeouts for the entire leader window.
- The timeout formula exactly matches Definition 17. Because the emitter enforces `IsFirstSlotOfWindow(slot)`, the schedule respects the “never in the past” guarantee `(i - s + 1) ≥ 1`.
- State modeling aligns with Definition 18: the hash associated with `ParentReady(hash(b))` is captured via `parentReady[slot]`, while the state flag tracks the presence of the event.

Overall, this handler is correct with respect to the whitepaper.

## 6. Open Questions / Concerns

- Defensive use of the window’s first slot in the formula:
  - The handler relies on the caller to pass the first slot of the window (true in `EmitParentReady`). If used elsewhere, `(i - slot + 1)` could underflow for earlier slots in the same window. Not a bug as written, but a latent hazard if re-used.

- Pending-blocks iteration granularity:
  - `CheckPendingBlocks` processes at most one pending block per slot per invocation, whereas the whitepaper models a single pending block per slot. This is a benign over-approximation but worth calling out. See `specs/tla/alpenglow/VotorCore.tla:141` and `alpenglow-whitepaper.md:625`.

## 7. Suggestions for Improvement

- Make the timeout arithmetic self-contained and robust:
  - Compute `first == FirstSlotOfWindow(slot)` and use `(i - first + 1)` and `WindowSlots(first)` inside the handler. This encodes the Definition 17 formula directly and reduces dependency on the caller’s precondition.

- Optional assertion/invariant for model checking:
  - Add an invariant (or `ASSUME` constraint near emission) that `IsFirstSlotOfWindow(slot)` holds when invoking `HandleParentReady`, or assert `timeouts[i] > clock` for all `i ∈ WindowSlots(slot)` after scheduling.

- Document the split state representation:
  - Add a brief comment near `ValidatorState.parentReady` pointing to Definition 18 to make it explicit that `ParentReady(hash(b))` content is carried via this field.

- Minor: intersection with `Slots` is redundant because `WindowSlots(slot)` already restricts to production slots (`specs/tla/alpenglow/Blocks.tla:211`). Keeping it is harmless; consider a comment stating this.

```text
Files referenced:
- specs/tla/alpenglow/VotorCore.tla:255
- specs/tla/alpenglow/MainProtocol.tla:675
- specs/tla/alpenglow/VoteStorage.tla:268
- specs/tla/alpenglow/Blocks.tla:211
- specs/tla/alpenglow/Messages.tla:19
- alpenglow-whitepaper.md:543
- alpenglow-whitepaper.md:546
- alpenglow-whitepaper.md:607
- alpenglow-whitepaper.md:609
- alpenglow-whitepaper.md:613
- alpenglow-whitepaper.md:615
- alpenglow-whitepaper.md:651
```

