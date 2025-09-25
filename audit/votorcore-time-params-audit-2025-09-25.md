# Audit: VotorCore timeout/block-time constants and module imports

## 1. Code Being Audited

```tla
EXTENDS Naturals, FiniteSets, Sequences, TLC, 
        Messages, Blocks, 
        Certificates, VoteStorage

CONSTANTS
    DeltaTimeout,   \* Timeout delay parameter (e.g., 3Δ)
    DeltaBlock      \* Block time parameter (e.g., 400ms)

ASSUME
    /\ DeltaTimeout \in Nat \ {0}
    /\ DeltaBlock \in Nat \ {0}
```

Context: This snippet is the header of `specs/tla/alpenglow/VotorCore.tla:1`, which implements the Votor voting state machine.

## 2. Whitepaper Sections and References

- Timeouts and timing parameters (source of `DeltaBlock` and `DeltaTimeout`):
  - alpenglow-whitepaper.md: Page 23, Definition 17 (Timeout) — schedule formula and parameter definitions.
  - The narrative around local clocks and timer semantics on Page 23.

- Votor state and event loop that rely on these timers:
  - alpenglow-whitepaper.md: Pages 23–25, Definition 18 and Algorithms 1–2 (SETTIMEOUTS, TRYNOTAR, TRYSKIPWINDOW, TRYFINAL).

- Code usage cross-references:
  - `specs/tla/alpenglow/VotorCore.tla:255` HandleParentReady — schedules timeouts using `DeltaTimeout` and `DeltaBlock`.
  - `specs/tla/alpenglow/MainProtocol.tla:902` TimeoutsInFuture invariant — aligns with Def. 17’s (i − s + 1) ≥ 1.
  - `specs/tla/alpenglow/MC.cfg:26`–`specs/tla/alpenglow/MC.cfg:27` — model assigns concrete values to these constants for TLC.

## 3. Reasoning and Whitepaper Alignment

- Abstraction intent:
  - The whitepaper abstracts timing via two global delays (Page 23, Def. 17):
    - `Δ_block`: protocol block time.
    - `Δ_timeout`: residual delay to cover leader observation and dissemination — a conservative global constant.
  - Timeouts for a leader window starting at first-slot `s` are scheduled as:
    `clock() + Δ_timeout + (i − s + 1) · Δ_block` for every slot `i` in that window.

- Spec mapping in code:
  - The constants `DeltaBlock` and `DeltaTimeout` are declared and constrained to positive naturals, matching the whitepaper’s role as positive delays.
  - In `HandleParentReady` (`specs/tla/alpenglow/VotorCore.tla:255`), timeouts are scheduled exactly per Def. 17:
    `timeout == val.clock + DeltaTimeout + ((s - slot + 1) * DeltaBlock)` where `slot` is the first slot `s` of the window and `s` ranges over `WindowSlots(slot)`.
  - Window and slot arithmetic is supplied by `Blocks` (e.g., `WindowSlots`, `IsFirstSlotOfWindow`) so `(i − s + 1) ≥ 1` holds on first-slot windows, as required by Def. 17.
  - `MainProtocol` asserts `TimeoutsInFuture` (`specs/tla/alpenglow/MainProtocol.tla:902`) to enforce that no timeout is set in the past, reflecting the note under Def. 17.

- External module imports and their roles (context for this header):
  - `Messages` — defines `Vote`/`VoteType` and constructors used by Votor to emit votes.
  - `Blocks` — provides `WindowSlots`, `IsFirstSlotOfWindow`, leader-window arithmetic that timeouts depend on.
  - `Certificates` — thresholds and certificate validity; not directly used in the header, but Votor’s guards rely on these via `VoteStorage` events.
  - `VoteStorage` — Pool logic (events like `ShouldEmitParentReady`) that triggers `HandleParentReady`, leading to timeout scheduling.
  - `Naturals`, `FiniteSets`, `Sequences`, `TLC` — standard primitives for types, recursion, and choice.

Conclusion of mapping: The header’s constants and imports equip VotorCore with exactly the abstractions needed to implement Def. 17 timing and the Algorithms 1–2 event loop, consistent with the whitepaper.

## 4. Audit Conclusion

- The declaration and positivity assumptions for `DeltaTimeout` and `DeltaBlock` correctly reflect the whitepaper’s timing abstraction (Def. 17). No extra constraints are required at the abstraction level.
- The imported modules are appropriate and necessary for the VotorCore behaviors that use these constants: `Blocks` for window arithmetic, `VoteStorage` for triggering `ParentReady`, and `Messages`/`Certificates` for vote/certificate typing.
- Downstream usage in `VotorCore.HandleParentReady` matches the Def. 17 scheduling formula exactly; `MainProtocol.TimeoutsInFuture` provides the corresponding invariant, matching the whitepaper’s note that timeouts are never scheduled in the past.
- Therefore, this code block is correct w.r.t. the whitepaper and the surrounding TLA+ modules.

## 5. Open Questions / Concerns

- Units/scale: The model treats `DeltaBlock` and `DeltaTimeout` as abstract time quanta. The whitepaper suggests `Δ_timeout` captures residual synchrony-related delay; while positivity suffices for the spec, a note on unit consistency (both in the same time base as `clock`) could prevent misconfiguration.
- Relationship between parameters: The whitepaper does not require a specific inequality between `Δ_timeout` and `Δ_block`. If operational guidance expects `Δ_timeout` ≥ network+processing slack, consider documenting this expectation near the constants for model readers.
- Global vs per-node: The constants are global. The whitepaper frames them as protocol parameters; this is consistent, but if future models consider heterogeneous clocks or adaptive Δ estimates, the constants might need to be generalized.

## 6. Suggestions for Improvement

- Documentation cross-link: Add an inline comment by the constants referencing Def. 17 in `alpenglow-whitepaper.md` to make the provenance explicit for readers new to the file.
- Optional typing guard (non-functional): In `MainProtocol` the `TimeoutsInFuture` invariant is already present; consider mirroring a brief comment near `HandleParentReady` noting the Def. 17 guarantee `(i − s + 1) ≥ 1` and why positivity suffices for non-past scheduling.
- Model parameter clarity: In `MC.cfg`, briefly comment that `DeltaTimeout` and `DeltaBlock` are sized for fast TLC exploration and do not encode real-world latencies; this helps avoid misinterpretation when reading model runs.

