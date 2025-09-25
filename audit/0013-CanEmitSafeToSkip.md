# Audit: CanEmitSafeToSkip (SafeToSkip event guard)

- Code reference: `specs/tla/alpenglow/VoteStorage.tla:308`
- Call site reference: `specs/tla/alpenglow/MainProtocol.tla:645`
- Supporting operators: `specs/tla/alpenglow/VoteStorage.tla:155` (SkipStake), `specs/tla/alpenglow/VoteStorage.tla:162` (TotalNotarStake), `specs/tla/alpenglow/VoteStorage.tla:169` (MaxNotarStake)
- Threshold check: `specs/tla/alpenglow/Certificates.tla:95` (MeetsThreshold)

## 1. Code Being Audited

```tla
CanEmitSafeToSkip(pool, slot, alreadyVoted, votedSkip) ==
    /\ alreadyVoted      \* Must have voted in slot
    /\ ~votedSkip        \* But not skip
    /\ LET skip == SkipStake(pool, slot)
           totalNotar == TotalNotarStake(pool, slot)
           maxNotar == MaxNotarStake(pool, slot)
       IN MeetsThreshold(skip + totalNotar - maxNotar, 40)
```

Context of use (emission site):

- `EmitSafeToSkip` emits the event and triggers a skip-fallback vote when the above predicate holds, provided the node hasn’t already produced a fallback in that slot and no skip certificate already exists: `specs/tla/alpenglow/MainProtocol.tla:645`.

## 2. Whitepaper Sections and References

- Definition 16 (fallback events): `alpenglow-whitepaper.md:554`–`:574` (pages 21–22)
  - SafeToSkip condition: `alpenglow-whitepaper.md:571`–`:574`
    - Formula: `skip(s) + \sum_b notar(b) − max_b notar(b) ≥ 40%`.
- Count-once-per-slot rule (Definition 12): `alpenglow-whitepaper.md:548`, referenced in the Def. 16 preamble at `:554`.
- Message types and thresholds (Tables 5–6): `alpenglow-whitepaper.md:493`–`:504` (skip vs skip-fallback vote distinction; skip certificate threshold 60%).

## 3. Reasoning and Mapping to the Whitepaper

What the whitepaper claims:

- SafeToSkip(s) indicates that no block in slot s can be fast-finalized, hence it’s safe to cast a skip-fallback vote (Def. 16). The inequality uses only initial votes: skip(s) and notar(b) (not fallback votes), and counts each validator’s stake at most once per slot (Def. 12).
- The guard is only evaluated after the node cast its initial vote in slot s, and only if that initial vote was not a skip vote.

How the code implements it:

- Gating preconditions:
  - `alreadyVoted` enforces “voted in slot s already”. In the call site, this is `HasState(_, s, "Voted")`, which corresponds to having cast an initial vote (notarization or skip) in s.
  - `~votedSkip` ensures the node did not cast an initial SkipVote for s. At the call site, `votedSkip` is true iff this validator has a `SkipVote` (not skip-fallback) in s.
- Inequality terms:
  - `SkipStake(pool, slot)` implements `skip(s)` as total stake of validators with an initial `SkipVote` in s (`specs/tla/alpenglow/VoteStorage.tla:155`). It intentionally excludes `SkipFallbackVote`, consistent with Def. 16 which uses initial votes for the guard.
  - `TotalNotarStake(pool, slot)` implements `\sum_b notar(b)` as the stake of validators who cast an initial `NotarVote` in s for any block (`:162`). The implementation deduplicates by validator identity, thereby respecting Def. 12’s “count once per slot”. This matches summing across blocks under the rule that a validator can contribute at most once per slot.
  - `MaxNotarStake(pool, slot)` implements `max_b notar(b)` as the maximum stake of `NotarVote`s on any single block b in s (`:169`).
- Threshold check:
  - `MeetsThreshold(x, 40)` implements `x ≥ 40%` w.r.t. `TotalStake` (`specs/tla/alpenglow/Certificates.tla:95`), using integer-safe `stake*100 ≥ TotalStake*40`.

Why this realizes the paper’s intent:

- Disjointness of initial votes (Def. 12) ensures `skip(s)` and `\sum_b notar(b)` do not double-count validators.
- Subtracting `max_b notar(b)` removes the largest single-block notar slice, yielding the weight of “everyone else” voting in ways incompatible with fast-finalization of a single block in s. If that residual plus `skip(s)` reaches 40%, no single block can still accumulate 80% `NotarVote` stake to fast-finalize given the one-vote-per-slot rule, thus it is safe to initiate skip-fallback.
- The guard excludes fallback votes by design, aligning with Def. 16’s use of initial votes only; fallback votes are consequences of this guard, not inputs to it.

Edge cases considered:

- No notarization votes: `MaxNotarStake = 0`, inequality reduces to `skip(s) ≥ 40%` as expected.
- Single-block notarization: `totalNotar = maxNotar`, inequality reduces to `skip(s) ≥ 40%`; again matches the formula.
- Multiple blocks notarized by disjoint sets: `totalNotar − maxNotar` precisely counts the non-max notar stake, consistent with the paper’s `\sum_b notar(b) − max_b` term.

## 4. Conclusion of the Audit

- The operator exactly encodes Definition 16 (SafeToSkip) from the whitepaper, including the 40% threshold and the “voted in slot but not skip” precondition.
- The mapping from the formula to code is direct and correct:
  - `skip(s)` ↔ `SkipStake(pool, slot)` (initial SkipVote only)
  - `\sum_b notar(b)` ↔ `TotalNotarStake(pool, slot)` (initial NotarVote across all blocks, deduped)
  - `max_b notar(b)` ↔ `MaxNotarStake(pool, slot)`
  - `≥ 40%` ↔ `MeetsThreshold(_, 40)`
- Count-once-per-slot semantics are preserved via the Pool’s storage rules and the stake calculators, matching Def. 12.
- The emission site adds reasonable suppression guards (`~HasSkipCert`, `~HasState(_, s, "BadWindow")`), which are consistent with the protocol but orthogonal to Def. 16.

Overall: correct by construction with respect to the whitepaper’s abstraction.

## 5. Open Questions or Concerns

- Terminology clarity (paper vs model): Def. 16 uses “skip votes” and “notarization votes” terminology. The model interprets these strictly as initial votes (`SkipVote`, `NotarVote`), excluding fallback votes. This matches the intended reading, but a short comment in the code near `CanEmitSafeToSkip` explicitly stating “initial votes only” would remove any ambiguity.
- Asynchrony and early fallback arrivals: It is possible that a node receives `SkipFallbackVote`s from others before it evaluates SafeToSkip (due to scheduling). The guard rightfully ignores these, per Def. 16. If the intent were to make the guard robust to such arrivals, the paper would need to say so; as written, the implementation is correct.
- Measurable invariants: The model does not currently include a property tying `CanEmitSafeToSkip` to the impossibility of fast-finalization in that slot. While this is proven in the paper, adding a TLA+ invariant would help machine-check the linkage.

## 6. Suggestions for Improvement

- Add an explanatory comment above `CanEmitSafeToSkip` noting that:
  - `skip(s)` and `notar(b)` in Def. 16 refer to initial votes only (not fallback), and
  - the one-vote-per-slot rule (Def. 12) is what makes `TotalNotarStake` a sound realization of `\sum_b notar(b)`.
- Optional readability helper:
  - Introduce `NonMaxNotarStake(pool, s) == TotalNotarStake(pool, s) - MaxNotarStake(pool, s)` and use it in the guard to mirror the formula and emphasize intent.
- Add a safety invariant in `MainProtocol.tla`:
  - “If `CanEmitSafeToSkip(pool, s, TRUE, FALSE)` holds for some correct node’s Pool, then no block in slot s can later obtain ≥80% `NotarVote` stake in that Pool.” This property would encode the paper’s safety rationale in the model.
- Cross-check guard usage:
  - The emission site already guards against re-emission via `BadWindow` and skip-cert presence. Consider an explicit comment tying these suppressions to Algorithms (1) and (2) in §2.6, for faster reader alignment.

