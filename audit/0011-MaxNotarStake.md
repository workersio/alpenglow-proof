# Audit: MaxNotarStake

## 1. Code Under Audit

```
MaxNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : v.type = "NotarVote"}
        blocks == {v.blockHash : v \in notarVotes}
    IN IF blocks = {} THEN 0
       ELSE LET stakes == {NotarStake(pool, slot, b) : b \in blocks}
            IN CHOOSE s \in stakes : \A s2 \in stakes : s >= s2
```

Reference in repo: `specs/tla/alpenglow/VoteStorage.tla:169`

## 2. Whitepaper Sections and References

- Definition 12 (storing votes; “count once” per slot): `alpenglow-whitepaper.md:513`
- Definition 16 (fallback events, SafeToSkip and SafeToNotar):
  - Notar/skip definitions and “count once” reminder: `alpenglow-whitepaper.md:554`
  - SafeToSkip condition: `alpenglow-whitepaper.md:571`

Context in spec using MaxNotarStake:

- SafeToSkip predicate uses this operator: `specs/tla/alpenglow/VoteStorage.tla:312`

## 3. Reasoning vs Whitepaper Claims

Intent from the paper:

- Definition 16 defines SafeToSkip(s) as: skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.
- notar(b) is the cumulative stake of notarization votes for block b in slot s, and any node’s stake is counted at most once per slot (by Def. 12).

What the operator does:

- Collects all votes for a slot via `GetVotesForSlot(pool, slot)` (repo: `specs/tla/alpenglow/VoteStorage.tla:142`).
- Filters to initial notarization votes only: `v.type = "NotarVote"` (excludes fallback votes), as required by Def. 16’s notar(b).
- Forms the set of blocks observed in notarization votes: `{v.blockHash : v ∈ notarVotes}`. Blocks with no notar votes are omitted (their notar(b) = 0), which does not affect max or sum semantics.
- Computes the stake per block via `NotarStake(pool, slot, b)` (repo: `specs/tla/alpenglow/VoteStorage.tla:147`). That operator:
  - Again filters to NotarVote for block b in slot s, takes validators `{v.validator : ...}`, and computes stake with `CalculateStake(validators)` (repo: `specs/tla/alpenglow/Certificates.tla:76`). This enforces the “count once per validator per slot” rule (Def. 12), because Pool stores at most one initial vote per validator per slot (repo: `specs/tla/alpenglow/VoteStorage.tla:60`).
- Selects the maximum stake value among the block stakes using CHOOSE over the finite set `stakes`. If there are ties, any maximum value is chosen; since the value itself is the maximum stake, all maxima are equal, so the result is well-defined as a scalar even if the maximizing block is not unique.
- Handles the empty case (no NotarVote seen): returns 0, matching max_b notar(b) = 0 when all notar(b) = 0.

Mapping to the paper’s formula SafeToSkip:

- The spec computes `skip + TotalNotarStake − MaxNotarStake` (repo: `specs/tla/alpenglow/VoteStorage.tla:312–314`). Here:
  - `TotalNotarStake` sums notar(b) over all b (deduplicated by validator) and equals Σ_b notar(b) (repo: `specs/tla/alpenglow/VoteStorage.tla:162–166`). Because a validator can only cast one NotarVote per slot (Def. 12), blocks’ voter sets are disjoint, so the total equals the sum across blocks.
  - `MaxNotarStake` implements max_b notar(b) exactly as above.
  - `SkipStake` computes skip(s) from SkipVote(s) only (repo: `specs/tla/alpenglow/VoteStorage.tla:156–159`).

Conclusion on alignment: The operator realizes the max_b notar(b) term in Definition 16 precisely, with correct exclusion of fallback votes and “count once” semantics ensured via Pool rules and the stake calculation.

## 4. Conclusion of the Audit

- Correctness: MaxNotarStake is faithful to the whitepaper’s Definition 16 notion of max_b notar(b). Its inputs and dependencies (GetVotesForSlot, NotarStake, CalculateStake) align with the type system and count-once semantics (Definition 12).
- Edge cases: Returns 0 when no notarization votes exist for the slot, which matches the intended interpretation for max over an empty set of positive stakes in this context and keeps SafeToSkip well-defined.
- Determinism: The value returned is uniquely determined (the numerical maximum). CHOOSE’s non-determinism only matters for picking among equal maxima, but the returned number is the same.

## 5. Open Questions or Concerns

- Domain visibility of blocks with zero notar stake: The operator considers only blocks that appear in notarization votes. This matches the math since absent blocks contribute 0 to both sum and max. If future spec variants require considering a predefined universe of candidate blocks per slot (including zero-stake ones), this operator remains correct for SafeToSkip but might need a comment to clarify intent.
- Explicit tie handling: If a future consumer needs the block(s) attaining the maximum, a companion operator returning the argmax set would be clearer than relying on CHOOSE over values.

## 6. Suggestions for Improvement

- Add a small helper for set maximum to improve readability and reuse:
  - Example: `MaxNat(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y` and use `MaxNat(stakes)`.
- Add a brief comment linking this operator to Definition 16 and SafeToSkip to aid readers (point to `alpenglow-whitepaper.md:571`).
- Optional: Strengthen a nearby invariant documenting that `stakes \subseteq Nat` (already implied by `CalculateStake: Validators → Nat`), to make CHOOSE over a numeric set explicit.

## 7. Referenced Definitions in the Spec

- `GetVotesForSlot(pool, slot)`: `specs/tla/alpenglow/VoteStorage.tla:142–143`
- `NotarStake(pool, slot, blockHash)`: `specs/tla/alpenglow/VoteStorage.tla:147–153`
- `CalculateStake(validatorSet)`: `specs/tla/alpenglow/Certificates.tla:76–92`
- Vote/message structure and types (`NotarVote`, `blockHash`, `Validators`): `specs/tla/alpenglow/Messages.tla:38–71`
- SafeToSkip using MaxNotarStake: `specs/tla/alpenglow/VoteStorage.tla:312–314`

