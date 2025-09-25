# Audit: NotarStake(pool, slot, blockHash)

## 1. Code Audited

```tla
NotarStake(pool, slot, blockHash) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : 
            v.type = "NotarVote" /\ v.blockHash = blockHash}
        validators == {v.validator : v \in notarVotes}
    IN CalculateStake(validators)
```

References in code:
- `GetVotesForSlot(pool, slot)` — defined in `specs/tla/alpenglow/VoteStorage.tla:142`.
- `CalculateStake(validators)` — defined in `specs/tla/alpenglow/Certificates.tla:76`.
- Types/fields `vote.type`, `vote.blockHash`, `vote.validator` — defined in `specs/tla/alpenglow/Messages.tla`.

## 2. Whitepaper Sections Represented

- §2.4 (Votes & Certificates); Table 6 thresholds for notarization-related certificates. The quantity “notar(b)” is the sum of stake from NotarVote messages for block b in slot s.
- §2.5 (Pool); Definition 12 (vote multiplicity: “count once per validator per slot” for initial Notar/Skip votes) and Definition 13 (certificate storage uniqueness).
- §2.5 (Fallback events); Definition 16 (SafeToNotar/SafeToSkip) uses conditions such as notar(b) ≥ 40% and skip(s) + notar(b) ≥ 60% with notar(b) ≥ 20%.
- Cross-referenced whitepaper anchors in repo:
  - Table 6 usage and implications: alpenglow-whitepaper.md:476, 502, 534.
  - Event definitions: alpenglow-whitepaper.md:545–552, 556, 571.
  - “Vote once per slot” reasoning: alpenglow-whitepaper.md:822.

## 3. Reasoning vs. Whitepaper Claims

- Purpose: NotarStake computes the absolute stake weight of validators that cast an initial NotarVote for a specific block `blockHash` in a given `slot`.
- Slot scoping: `GetVotesForSlot(pool, slot)` unions all validators’ votes for that slot only, preventing cross-slot contamination.
- Vote filtering: `{ v ∈ votes : v.type = "NotarVote" ∧ v.blockHash = blockHash }` restricts to initial approval votes for the exact block. This matches “notar(b)” in §2.5 Def. 16 and the Notarization rows in Table 6 (§2.4), both of which are defined on initial NotarVote messages.
- Count-once-per-slot: The set `validators == { v.validator : v ∈ notarVotes }` deduplicates validators. Coupled with Pool multiplicity rules (VoteStorage.CanStoreVote enforces at most one initial Notar/Skip per validator per slot; whitepaper Def. 12), each validator’s stake contributes at most once to `notar(b)`.
- Stake aggregation: `CalculateStake(validators)` sums ρ_v from `StakeMap` for validators (Certificates.tla). `MeetsThreshold` elsewhere compares these sums to percentages of `TotalStake` matching Table 6 (60%, 80%) and Def. 16 (20%, 40%, 60%). NotarStake returns the Σ used by those checks.
- Interactions:
  - SafeToNotar (VoteStorage.CanEmitSafeToNotar) uses `notar := NotarStake(pool, slot, blockHash)` and `skip := SkipStake(pool, slot)` to implement the paper’s guard: notar ≥ 40% OR (skip + notar ≥ 60% AND notar ≥ 20%).
  - SafeToSkip uses totals derived from initial NotarVote counts per block, consistent with whitepaper: skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.

Conclusion of reasoning: The function computes exactly the intended “notar(b)” per the paper using only initial NotarVote messages, with count-once semantics and correct stake summation.

## 4. Audit Conclusion

- Correctness: Matches the whitepaper’s abstraction. NotarStake returns the per-block initial notarization stake for a slot, consistent with:
  - Table 6’s use of NotarVote-only for notarization thresholds.
  - Definition 16’s guards referring to notar(b) and skip(s) in terms of initial votes.
  - Definition 12’s “count-once-per-slot” rule via validator set deduplication and Pool multiplicity constraints.
- Cross-module consistency: `GetVotesForSlot` (slot-scoped), `CalculateStake` (Σ ρ_v over unique validators), and `StakeMap` typing assumptions align with the intended semantics.

Therefore, NotarStake is a faithful and precise specification of the whitepaper notion of notar(b).

## 5. Open Questions / Concerns

- Explicit slot check redundancy: NotarStake relies on `GetVotesForSlot(pool, slot)` for slot scoping. While correct, an additional explicit filter `v.slot = slot` would make the function robust to accidental misuse if `GetVotesForSlot` were replaced/modified. This is stylistic, not a correctness issue today.
- Parameter validity: The function assumes `blockHash ∈ BlockHashes`. Callers (e.g., SafeToNotar and certificate guards) already ensure this via their own context. A defensive precondition is unnecessary in TLA+ but could be documented.
- Naming clarity: The term “NotarStake” is used only for initial notar votes (NotarVote). This matches the paper, but adding a brief note “initial votes only” near the definition can prevent misinterpretation.

## 6. Suggestions for Improvement

- Minor readability refactor: Replace the manual validator projection with the existing aggregation helper for consistency:
  - Use `StakeFromVotes({ v ∈ votes: v.type = "NotarVote" ∧ v.blockHash = blockHash })` (from Certificates.tla) so the “count once” policy is uniformly encoded via `UniqueValidators`.
- Optional explicit slot guard:
  - Inline `v.slot = slot` in the comprehension, even though `GetVotesForSlot` already scopes by slot. This is belt-and-suspenders clarity.
- Local assertion (optional): Add a declarative check tying this function to its vote-based counterpart for sanity during model exploration:
  - `Assert( NotarStake(pool, s, b) = StakeFromVotes({ v ∈ GetVotesForSlot(pool, s) : v.type = "NotarVote" ∧ v.blockHash = b }) )` in comments or as an invariant in debug configs.
- Comment cross-links: Add a brief whitepaper citation just above the definition (e.g., “Whitepaper §2.5 Def. 16: notar(b)”). This is already hinted by nearby comments; making it explicit improves traceability.

