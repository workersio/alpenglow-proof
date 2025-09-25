# Audit: TotalNotarStake(pool, slot)

## 1. Code Under Audit

```tla
TotalNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : v.type = "NotarVote"}
        validators == {v.validator : v \in notarVotes}
    IN CalculateStake(validators)
```

Source: specs/tla/alpenglow/VoteStorage.tla:161–166

## 2. Whitepaper Sections/References Represented

- Pool and multiplicity (count-once-per-slot): alpenglow-whitepaper.md:509–519 (Definition 12)
- Certificate thresholds and vote types (context): alpenglow-whitepaper.md:500–507 (Table 6)
- Fallback events (uses notar(b), skip(s) and Σ_b notar(b)): alpenglow-whitepaper.md:554–574 (Definition 16)
  - SafeToSkip inequality: alpenglow-whitepaper.md:571–574

## 3. Reasoning and Alignment With Whitepaper

- Purpose in the model
  - This operator computes Σ_b notar(b) for a given slot s, as required by Definition 16’s SafeToSkip inequality: skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.
  - It is used by CanEmitSafeToSkip: specs/tla/alpenglow/VoteStorage.tla:308–315.

- References and their semantics
  - GetVotesForSlot(pool, slot): specs/tla/alpenglow/VoteStorage.tla:142–144
    - Returns all votes in Pool for slot s across validators.
  - NotarVote type and vote structure: specs/tla/alpenglow/Messages.tla:44–58
    - NotarVote is the initial approval vote used to define notar(b) in the paper.
  - CalculateStake(validatorSet): specs/tla/alpenglow/Certificates.tla:76–84
    - Sums stake ρ_v from StakeMap for validators in the set; ignores non-members safely via intersection with DOMAIN StakeMap.

- Count once per slot
  - Definition 12 requires a validator’s stake be counted at most once per slot. The code enforces this by projecting votes to validator identities: validators == {v.validator : v ∈ notarVotes} and then summing stake over the set (deduplicated) of validators.
  - Pool’s storage rules (CanStoreVote) admit at most one initial vote (NotarVote or SkipVote) per validator per slot, consistent with Lemma 20 commentary in the whitepaper. The set projection defensively preserves “count once” even if storage logic changed.

- Using NotarVote (not fallback)
  - Definition 16 defines notar(b) specifically via notarization votes for b that are in Pool; this corresponds to NotarVote only, not NotarFallbackVote. The code filters exactly v.type = "NotarVote", matching the paper’s definition.

- Σ_b notar(b) realized as unique-notar-voters
  - Since Pool stores at most one NotarVote per validator per slot (Definition 12; CanStoreVote), the union across all blocks of per-block notar(b) totals equals the stake of all validators who cast a NotarVote in s. TotalNotarStake computes precisely this value by collecting all NotarVote voters (across all blocks) and summing their stake once.
  - This aligns with the SafeToSkip formula’s intended meaning: “how much stake voted for any block in this slot, regardless of which block,” without double-counting validators.

## 4. Conclusion

- The definition of TotalNotarStake(pool, slot) is correct and faithful to the whitepaper’s abstractions:
  - It counts each validator at most once per slot (Definition 12), by projecting to a set of validators.
  - It uses only NotarVote to match the whitepaper’s notar(b) definition (Definition 16).
  - It provides the Σ_b notar(b) term used by CanEmitSafeToSkip (Definition 16) and is coherent with MaxNotarStake (per-block maximum) and SkipStake.

No safety or liveness mismatches were found with respect to the paper in this operator.

## 5. Open Questions / Concerns

- Byzantine equivocation across blocks:
  - Although adversaries may send multiple NotarVote messages for different blocks, Pool (per Definition 12) stores only the first initial vote per validator per slot. This makes Σ_b notar(b) node‑local and depends on message arrival order. This is acceptable per the paper (events are local), but worth noting as an intentional modeling choice.

- Terminology clarity:
  - The paper’s “notar(b)” specifically uses initial notarization votes. If at some future point we generalize to include fallback votes in other contexts, ensure formulas that refer to notar(b) remain tied to NotarVote only unless explicitly stated otherwise.

## 6. Suggestions for Improvement

- Refactor for reuse and clarity:
  - Consider defining TotalNotarStake using Certificates.StakeFromVotes to centralize deduplication and stake logic:
    ```tla
    TotalNotarStake(pool, slot) ==
        LET votes == GetVotesForSlot(pool, slot)
            notarVotes == {v \in votes : v.type = "NotarVote"}
        IN StakeFromVotes(notarVotes)
    ```
    StakeFromVotes(votes) already enforces the “count once per slot” projection and uses CalculateStake consistently.

- Documentation nudge:
  - Add a brief comment at the definition site referencing Definition 16 and stating that this operator corresponds to Σ_b notar(b) with count‑once semantics per Definition 12. This makes the intent explicit where it is used.

- Optional invariant (sanity):
  - For any slot s, with blocks B_s that have NotarVote in Pool, assert that TotalNotarStake(pool, s) = CalculateStake({v ∈ Validators : ∃ vt ∈ GetVotesForSlot(pool, s). vt.type = "NotarVote" ∧ vt.validator = v}). This is tautological with the current definition, but if refactored to StakeFromVotes, an invariant helps guard against regressions.

