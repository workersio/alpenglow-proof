# Audit: EmitSafeToSkip (TLA+)

1. Code that you are auditing

```tla
EmitSafeToSkip ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot :
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedSkip == 
                    \E vt \in GetVotesForSlot(validators[v].pool, s) :
                        /\ vt.validator = v
                        /\ vt.type = "SkipVote"
            IN CanEmitSafeToSkip(validators[v].pool, s, alreadyVoted, votedSkip)
         /\ ~HasState(validators[v], s, "BadWindow")
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToSkip(@, s)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>
```

2. Whitepaper sections and references represented by the code

- Definition 16 (fallback events) — SafeToSkip(s) preconditions and inequality: alpenglow-whitepaper.md: Page 22.
- Definition 12 (Pool multiplicity / count-once-per-slot): alpenglow-whitepaper.md: Page 20–21.
- Algorithm 1 (event handlers), lines 21–25: SafeToSkip handler logic: alpenglow-whitepaper.md:23.
- Related state objects (Voted, BadWindow, ItsOver): alpenglow-whitepaper.md:23 (bulleted state definitions and lines 20, 25 for adding BadWindow).

3. Reasoning: how the code implements the whitepaper

- Event guard matches Definition 16.
  - Requires prior initial vote in slot s but not a skip vote: `alreadyVoted` uses `HasState(..., "Voted")`; `votedSkip` checks local pool for a `SkipVote` by v in s. This implements “voted already, but not to skip s.”
  - Mathematical condition: `CanEmitSafeToSkip(pool, s, ...)` enforces the fallback inequality from Definition 16: `skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%` via stake aggregation helpers `SkipStake`, `TotalNotarStake`, `MaxNotarStake` and `MeetsThreshold(..., 40)` (specs/tla/alpenglow/VoteStorage.tla:299).
- Single-shot semantics via BadWindow.
  - The `~HasState(..., "BadWindow")` guard ensures the fallback event is emitted at most once per slot per validator, matching Algorithm 1 where casting a fallback vote adds `BadWindow` (thus suppressing repeated fallback behavior).
- State transition implements Algorithm 1 lines 21–25.
  - `HandleSafeToSkip(@, s)` performs `TRYSKIPWINDOW(s)` and, if `ItsOver ∉ state[s]`, broadcasts a `SkipFallbackVote(s)` and adds `BadWindow` (specs/tla/alpenglow/VotorCore.tla:288). This mirrors Algorithm 1 lines 21–25 exactly.
- Dissemination is decoupled.
  - `HandleSafeToSkip` stores the `SkipFallbackVote` locally; `BroadcastLocalVote` later injects locally stored votes into the network (`messages`) under weak fairness (specs/tla/alpenglow/MainProtocol.tla:319). This models the “broadcast to all other nodes” assumption.
- Slot/window interactions are respected.
  - `TRYSKIPWINDOW(s)` issues `SkipVote(k)` for every unvoted slot k in the leader window, and marks `{Voted, BadWindow}` (specs/tla/alpenglow/VotorCore.tla:161), matching Algorithm 2 lines 22–27.

References in code (starting line numbers):
- Event under audit: specs/tla/alpenglow/MainProtocol.tla:365.
- Fallback predicate: `CanEmitSafeToSkip` specs/tla/alpenglow/VoteStorage.tla:299.
- Stake helpers: `SkipStake` 152, `TotalNotarStake` 159, `MaxNotarStake` 166 in VoteStorage.tla.
- State checks: `HasState` specs/tla/alpenglow/VotorCore.tla:79.
- Event handler: `HandleSafeToSkip` specs/tla/alpenglow/VotorCore.tla:288.
- Window skip helper: `TrySkipWindow` specs/tla/alpenglow/VotorCore.tla:161.
- Vote constructors: `CreateSkipFallbackVote` specs/tla/alpenglow/Messages.tla:87.

4. Conclusion of the audit

- Correctness vs. whitepaper: The EmitSafeToSkip action, its guard, and its handler correctly implement Definition 16 (SafeToSkip) and Algorithm 1 (lines 21–25). The inequality and preconditions are faithful, and the handler behavior (TRYSKIPWINDOW; emit SkipFallbackVote; add BadWindow) matches the pseudocode. The decoupled broadcast mechanism aligns with the whitepaper’s dissemination model.
- Safety intent: By requiring `skip + totalNotar − maxNotar ≥ 40%`, the spec ensures no block can reach the 80% fast-finalization threshold, consistent with the whitepaper’s rationale for SafeToSkip.

5. Open questions or concerns

- Critical: Definition 12 “count-once-per-slot” is not fully enforced across initial vote types in Pool storage.
  - Whitepaper text: “The first received notarization or skip vote” (singular per slot, not per type).
  - Current spec allows storing one NotarVote and one SkipVote for the same validator and slot (per-type limits only), see `CanStoreVote` (specs/tla/alpenglow/VoteStorage.tla:120–138). This violates Definition 12 and permits a Byzantine validator to contribute to both `SkipStake` and `TotalNotarStake` for the SafeToSkip inequality, effectively double-counting across types.
  - Consequence: The SafeToSkip guard may be satisfied prematurely because a validator’s stake is counted both in `skip(s)` and in `Σ notar(b)` when summing, contrary to “count once per slot”. This undermines the soundness of the fallback inequality in adversarial settings.
- Minor: `votedSkip` checks for the presence of an initial `SkipVote` (not `SkipFallbackVote`). This is correct per Definition 16 language, and repeated emission is prevented by the `BadWindow` guard. Calling this out explicitly in comments might help future readers.
- Idempotence vs. existing certificates: The action does not guard on `HasSkipCert(slot)`. While harmless (certificate storage is unique and further votes won’t create duplicates), you could optionally short-circuit if a skip certificate is already present to avoid unnecessary local vote storage/broadcasts.

6. Suggestions for improvement

- Fix Pool multiplicity to enforce cross-type uniqueness for initial votes (align with Definition 12):
  - In `CanStoreVote(pool, vote)` (specs/tla/alpenglow/VoteStorage.tla:120–138), change the guards to prevent storing a `SkipVote` if a `NotarVote` already exists for the (validator, slot), and vice versa. For example:
    - For `NotarVote`: require no existing `NotarVote` and no existing `SkipVote`.
    - For `SkipVote`: require no existing `SkipVote` and no existing `NotarVote`.
  - This ensures a validator contributes at most once per slot across initial types, eliminating double-counting in the SafeToSkip inequality and making Pool strictly compliant with Definition 12.
- Optional defensive guard in event emission:
  - Add `\/ ~HasSkipCert(validators[v].pool, s)` to `EmitSafeToSkip` to skip redundant fallback voting when a skip certificate for s already exists. This does not change correctness but can simplify traces and model checking.
- Documentation clarity:
  - Augment comments around `votedSkip` in `EmitSafeToSkip` to state explicitly that skip-fallback eligibility excludes validators who initially skipped; repeated fallback emission is suppressed by `BadWindow`.

Overall, with the proposed fix to initial vote multiplicity, the EmitSafeToSkip path accurately captures the whitepaper’s abstractions and safety reasoning.
