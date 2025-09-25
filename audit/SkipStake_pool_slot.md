# Audit: SkipStake(pool, slot)

## 1. Code Under Audit

Origin in repo: `specs/tla/alpenglow/VoteStorage.tla:155`

```tla
SkipStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        skipVotes == {v \in votes : v.type = "SkipVote"}
        validators == {v.validator : v \in skipVotes}
    IN CalculateStake(validators)
```

Referenced functions and types:
- `GetVotesForSlot`: `specs/tla/alpenglow/VoteStorage.tla:142`
- `CalculateStake`: `specs/tla/alpenglow/Certificates.tla:76`
- Vote types incl. `"SkipVote"`: `specs/tla/alpenglow/Messages.tla:32–62`

Direct usages of `SkipStake` in safety gating (for context):
- `CanEmitSafeToNotar`: `specs/tla/alpenglow/VoteStorage.tla:283`
- `CanEmitSafeToSkip`: `specs/tla/alpenglow/VoteStorage.tla:308`

## 2. Whitepaper Sections and References Represented

- Section 2.5 Pool (Pages 20–21)
  - Definition 12 (storing votes): “Pool stores … The first received notarization or skip vote, …” and “count each node’s stake at most once per slot.”
- Section 2.5 Pool (Pages 21–22)
  - Definition 16 (fallback events): Defines
    - skip(s): “cumulative stake of nodes whose skip votes for slot s are in Pool”
    - notar(b): “cumulative stake of nodes whose notarization votes for block b are in Pool”
    - SafeToNotar condition: notar(b) ≥ 40% OR (skip(s)+notar(b) ≥ 60% AND notar(b) ≥ 20%)
    - SafeToSkip condition: skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%
- Tables 5–6 (Section 2.4, Page 20): Enumerate vote and certificate types; SkipCert can aggregate SkipVote or SkipFallbackVote at ≥60% (contextual contrast with skip(s)).

## 3. Reasoning vs. Whitepaper Claims

- What SkipStake computes:
  - Gathers all votes in `slot` via `GetVotesForSlot(pool, slot)` (Pool-sourced set, includes both initial and fallback votes stored under Definition 12 multiplicity rules).
  - Filters to initial skip votes only: `{ v ∈ votes : v.type = "SkipVote" }`.
  - Deduplicates by validator: `{ v.validator : v ∈ skipVotes }`.
  - Aggregates stake once per validator using `CalculateStake` (sums `ρ_v` from `StakeMap`).

- Alignment with Definition 16 (“skip(s)”):
  - Whitepaper defines skip(s) using skip votes (initial), not skip-fallback votes. The code uses only `"SkipVote"`, correctly excluding `"SkipFallbackVote"`.
  - “Count once per slot” is satisfied by taking a set of validators before summation; even if multiple skip votes per validator slipped in, deduplication limits stake to once per validator. In practice, Definition 12 already prevents multiple initial votes per validator per slot.

- Interplay with gating conditions (Def. 16):
  - `CanEmitSafeToNotar` uses `skip := SkipStake(pool, slot)` together with `notar := NotarStake(pool, slot, blockHash)` and threshold checks. Because a validator can cast exactly one initial vote per slot (Lemma 20; enforced by Pool), skip and notar sets are disjoint, avoiding double counting.
  - `CanEmitSafeToSkip` uses `skip := SkipStake(pool, slot)` and totals over initial notar votes (`TotalNotarStake`, `MaxNotarStake`), matching the formula skip(s)+Σ notar−max notar ≥ 40%.

- Separation from SkipCert construction (Table 6):
  - SkipCert thresholds (≥60%) may aggregate both `SkipVote` and `SkipFallbackVote` (via `IsSkipVote`). This is intentionally different from `SkipStake`, which must reflect only initial skip votes for safety gating per Definition 16.

## 4. Conclusion of the Audit

- The `SkipStake` definition matches the whitepaper’s Definition 16: it measures skip(s) as the cumulative stake of validators who cast initial skip votes in slot s, counting each validator at most once.
- It composes correctly with the Pool’s storage rules (Definition 12) and with the event guards `CanEmitSafeToNotar` and `CanEmitSafeToSkip` that implement the fallback thresholds.
- The use of `CalculateStake` ensures stake weights are summed correctly and only for validators in `StakeMap`, satisfying the “count-once-per-slot” principle.

## 5. Open Questions or Concerns

- Naming clarity: `SkipStake` counts only initial skip votes. Given that `IsSkipVote` elsewhere includes both initial and fallback, the function name could be misread as “all skip stake”. The current implementation is correct, but a more explicit name or comment would reduce ambiguity.
- Defensive domain checks: `SkipStake` assumes `slot ∈ Slots` and that Pool is well-typed. This is standard in TLA+, but if reused more broadly, documenting this precondition inline would help readers.
- Adversarial timing: Because `SkipStake` intentionally ignores skip-fallback votes, Byzantine attempts to inflate skip(s) via fallback votes do not affect safety gating. This is desirable and matches the whitepaper, but it’s worth calling out as a deliberate choice in comments.

## 6. Suggestions for Improvement

- Add an explicit comment above `SkipStake` to tie it to Definition 16 and to clarify that it counts initial skip votes only (not skip-fallback):
  - Example: “Per Def. 16, skip(s) counts only initial SkipVote; SkipFallbackVote is excluded.”
- Optionally rename or alias for readability:
  - Keep `SkipStake` and add `InitialSkipStake == SkipStake` (or vice versa) to emphasize the “initial” semantics used in fallback gating.
- Add a small lemma or invariant in VoteStorage documenting the relationship used by SafeToSkip:
  - e.g., `SkipStake(pool, s) + TotalNotarStake(pool, s) - MaxNotarStake(pool, s) >= 0` and that each term respects count-once-by-validator, to aid proofs.

Overall, no changes are required for correctness relative to the whitepaper; suggestions are for clarity and proof convenience only.

