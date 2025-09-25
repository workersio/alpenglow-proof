# Audit: HandleSafeToSkip (VotorCore)

- File reference: `specs/tla/alpenglow/VotorCore.tla:292`

## 1) Code That You Are Auditing

```tla
HandleSafeToSkip(validator, slot) ==
    LET skipResult == TrySkipWindow(validator, slot)
    IN
        IF ~HasState(skipResult, slot, "ItsOver") THEN
            LET vote == CreateSkipFallbackVote(skipResult.id, slot)
                newValidator == AddState(skipResult, slot, "BadWindow")
                poolWithVote == StoreVote(newValidator.pool, vote)
            IN [newValidator EXCEPT !.pool = poolWithVote]
        ELSE skipResult
```

## 2) Whitepaper Sections And References

- Definition 16 (fallback events): SafeToSkip preconditions and inequality
  - `alpenglow-whitepaper.md:571` — SafeToSkip(s) precondition text
  - `alpenglow-whitepaper.md:573` — Formula: skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%
- Algorithm 1 (event loop), SafeToSkip handler (lines 21–25)
  - `alpenglow-whitepaper.md:662` — upon SafeToSkip(s)
  - `alpenglow-whitepaper.md:663` — TRYSKIPWINDOW(s)
  - `alpenglow-whitepaper.md:664` — if ItsOver ∉ state[s]
  - `alpenglow-whitepaper.md:665` — broadcast SkipFallbackVote(s)
  - `alpenglow-whitepaper.md:666` — state[s] ← state[s] ∪ {BadWindow}
- Definition 18 (Votor state objects)
  - `alpenglow-whitepaper.md:621` — ItsOver
  - `alpenglow-whitepaper.md:630` — BadWindow
- Definition 12 (storing votes; multiplicity rules)
  - `alpenglow-whitepaper.md:516` — “up to 3 notar-fallback votes”
  - `alpenglow-whitepaper.md:517` — “the first received skip-fallback vote”
- Table 5 (messages) — SkipFallbackVote
  - `alpenglow-whitepaper.md:494` — Skip-Fallback Vote row
- Algorithm 2 (helpers) — TRYSKIPWINDOW(s)
  - `alpenglow-whitepaper.md:705`–`alpenglow-whitepaper.md:710` — skip unvoted slots, add {Voted, BadWindow}, clear pending

## 3) References In Code (Cross-Module)

- `TrySkipWindow` — skips all unvoted slots in the window; adds {Voted, BadWindow}; clears pending
  - Definition: `specs/tla/alpenglow/VotorCore.tla:163`
  - Whitepaper alignment: Alg. 2 lines 22–27 (`alpenglow-whitepaper.md:705`–`:710`)
- `HasState` — state membership helper (per-slot flags per Definition 18)
  - Definition: `specs/tla/alpenglow/VotorCore.tla:81`
- `CreateSkipFallbackVote` — constructs a Skip-Fallback vote message
  - Definition: `specs/tla/alpenglow/Messages.tla:90`
  - Whitepaper Table 5: `alpenglow-whitepaper.md:494`
- `AddState` — adds a state flag to the per-slot state set
  - Definition: `specs/tla/alpenglow/VotorCore.tla:85`
- `StoreVote` — stores a vote in the per-validator Pool respecting Def. 12 multiplicity
  - Definition: `specs/tla/alpenglow/VoteStorage.tla:84`
  - Def. 12 multiplicity: `alpenglow-whitepaper.md:516`–`:517`
- Event emission context (who calls this handler): `EmitSafeToSkip`
  - Emission guard: `specs/tla/alpenglow/MainProtocol.tla:645`–`:657`
  - Inequality predicate: `specs/tla/alpenglow/VoteStorage.tla:306`–`:314` (CanEmitSafeToSkip)

## 4) Reasoning: What The Code Does vs. The Whitepaper

- Step A — Perform TRYSKIPWINDOW(s): The handler first computes `skipResult == TrySkipWindow(validator, slot)`, which emits SkipVote for any unvoted slots in the same window, adds {Voted, BadWindow} to those slots, and clears their pending blocks. This exactly matches Algorithm 1, line 22 and Algorithm 2, lines 23–27 (`alpenglow-whitepaper.md:663`, `:705`–`:710`). Importantly, because SafeToSkip’s emission precondition requires “already voted in s, but not to skip s” (`alpenglow-whitepaper.md:571`), TrySkipWindow will not cast an initial skip for s itself — it only affects other unvoted slots in the window.

- Step B — Guard on ItsOver: The code checks `~HasState(skipResult, slot, "ItsOver")`. This implements Algorithm 1, line 23 (`alpenglow-whitepaper.md:664`), ensuring that once the finalization vote is cast for slot s, no fallback votes are produced thereafter.

- Step C — Cast Skip-Fallback and mark BadWindow: If not ItsOver, the handler creates a `SkipFallbackVote` for s, adds `BadWindow` to state[s], and stores the new vote in the Pool. This mirrors Algorithm 1, lines 24–25 (`alpenglow-whitepaper.md:665`–`:666`). Adding `BadWindow` is consistent with Definition 18 (`alpenglow-whitepaper.md:630`) meaning “cast skip/skip-fallback/notar-fallback in this slot.” In turn, `BadWindow` suppresses future `TRYFINAL` for s, matching Algorithm 2, line 19’s guard and its TLA encoding (`specs/tla/alpenglow/VotorCore.tla:141`–`:150`).

- Step D — Pool multiplicity and certificate consistency: `StoreVote` enforces Definition 12 (first SkipFallback per validator per slot), preventing redundant fallback storage (`alpenglow-whitepaper.md:517`; `specs/tla/alpenglow/VoteStorage.tla:84`). Certificates aggregate skip votes and skip-fallback votes equally (Table 6; modeled by `CanCreateSkipCert`), which is consistent with whitepaper semantics.

- Step E — Event emission preconditions (context): Although the handler does not re-check Definition 16, event emission is guarded elsewhere: `EmitSafeToSkip` uses `CanEmitSafeToSkip` with exactly the whitepaper inequality and preconditions (`specs/tla/alpenglow/MainProtocol.tla:645`–`:657`; `specs/tla/alpenglow/VoteStorage.tla:306`–`:314`). This separation of concerns is faithful to the paper: Pool emits SafeToSkip based on stake conditions; the event loop handler performs Alg. 1 actions.

Conclusion of reasoning: The handler is a faithful, line-by-line transcription of Algorithm 1, lines 21–25, and interacts correctly with Algorithm 2 and Definitions 12, 16, and 18.

## 5) Conclusion Of The Audit

- Correctness with respect to the whitepaper: PASS
  - Implements Algorithm 1 (SafeToSkip handler) exactly: TRYSKIPWINDOW; if not ItsOver, broadcast SkipFallbackVote; add BadWindow.
  - Respects Definition 12 (vote multiplicity) via StoreVote.
  - Respects Definition 18 (state flags): uses ItsOver and BadWindow consistently; BadWindow prevents finalization (as required by Alg. 2 TRYFINAL guards).
  - Emission conditions (Definition 16 inequality and “already voted but not skip” precondition) are enforced where the event is emitted, not in the handler, which aligns with the spec’s division of responsibilities.

No divergence from the whitepaper was found in this handler.

## 6) Open Questions Or Concerns

- Pending blocks for slot s after fallback: TRYSKIPWINDOW clears `pendingBlocks[k]` for each newly skipped slot k, but the SafeToSkip handler does not clear `pendingBlocks[s]` when issuing a skip-fallback (by design, s was already Voted, so pendingBlocks[s] should normally be ⊥). This is consistent with Algorithm 1 (no instruction to clear), but leaves a theoretical possibility of stale entries if some implementation pre-populated `pendingBlocks[s]` before the initial vote. It does not affect safety in the TLA abstraction (TRYNOTAR refuses once Voted is set).

- Re-entrancy/redundancy guards: The handler relies on emission guards (`~BadWindow`, `~HasSkipCert`) in `EmitSafeToSkip`. While this is faithful to the paper’s intent, adding a defensive `~HasState(validator, s, "BadWindow")` check in the handler would be harmless and further suppress redundant local work if the handler were ever called out-of-contract.

## 7) Suggestions For Improvement

- Optional clarity: Add an inline comment near the `TrySkipWindow` call in this handler stating that, due to the event emission precondition “already voted in s,” TRYSKIPWINDOW will not skip s itself, only other unvoted slots in the window. This aids readers connecting Definition 16 to Algorithm 1.

- Defensive guard (non-functional): Consider adding a no-op early return when `HasState(validator, slot, "BadWindow")` holds. Event emission already enforces this; duplicating it in the handler can reduce accidental reprocessing in extended models.

- Optional invariant (verification aid): Add a module-level invariant stating that once `BadWindow ∈ state[s]`, no `FinalVote(s)` is stored for that validator. This is already implied by `TryFinal`’s guard and Pool multiplicity, but an explicit invariant can make the safety argument more transparent during model checking.

- Hygiene (non-normative): If desired, clear `pendingBlocks[s]` after issuing a SkipFallbackVote. This is not required by the whitepaper and has no effect on behavior in this abstraction; it may help reduce model-state size in some scenarios.

## 8) Traceability Checklist

- Handler ↔ Algorithm 1 lines 21–25: `alpenglow-whitepaper.md:662`–`:666` ✓
- TRYSKIPWINDOW ↔ Algorithm 2 lines 22–27: `alpenglow-whitepaper.md:705`–`:710` ✓
- SkipFallbackVote message ↔ Table 5: `alpenglow-whitepaper.md:494` ✓
- Multiplicity (first SkipFallback per validator/slot) ↔ Definition 12: `alpenglow-whitepaper.md:517` ✓
- State flags (ItsOver, BadWindow) ↔ Definition 18: `alpenglow-whitepaper.md:621`, `:630` ✓
- Emission guard (Definition 16 inequality) ↔ `CanEmitSafeToSkip`: `specs/tla/alpenglow/VoteStorage.tla:306`–`:314` ✓

