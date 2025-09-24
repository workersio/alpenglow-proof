**Code Under Audit**

```
UniqueValidators(votes) ==
    {v.validator : v \in votes}

\* Calculate total stake from votes (counting each validator once!)
StakeFromVotes(votes) ==
    CalculateStake(UniqueValidators(votes))

\* Check if stake meets a percentage threshold
MeetsThreshold(stake, thresholdPercent) ==
    stake * 100 >= TotalStake * thresholdPercent
```

**Whitepaper References**

- Definition 11 (messages, certificate thresholds): alpenglow-whitepaper.md:478, alpenglow-whitepaper.md:501, alpenglow-whitepaper.md:502, alpenglow-whitepaper.md:505
- Table 6 explanation (Σ is cumulative stake of certificate votes): alpenglow-whitepaper.md:507
- Definition 12 (storing votes; “count once per slot”): alpenglow-whitepaper.md:513
- Restatement of “count once per slot” in fallback events: alpenglow-whitepaper.md:554
- Fast implies notar/fallback implication (consistency with thresholds): alpenglow-whitepaper.md:534

Related spec cross-refs for context:
- `StakeMap` typing and positivity: specs/tla/alpenglow/Certificates.tla:23
- `TotalStake`: specs/tla/alpenglow/Certificates.tla:38
- `CalculateStake`: specs/tla/alpenglow/Certificates.tla:49
- Vote record includes a `validator` field: specs/tla/alpenglow/Messages.tla:54
- Usage of these operators in certificate predicates: specs/tla/alpenglow/Certificates.tla:83, specs/tla/alpenglow/Certificates.tla:98, specs/tla/alpenglow/Certificates.tla:112, specs/tla/alpenglow/Certificates.tla:126, specs/tla/alpenglow/Certificates.tla:140

**Reasoning and Whitepaper Alignment**

- Unique validator extraction
  - `UniqueValidators` builds `{v.validator : v \in votes}` (specs/tla/alpenglow/Certificates.tla:60). This enforces the whitepaper’s “count once per slot” rule by collapsing multiple votes from the same validator into a single contribution when computing stake.
  - The vote structure guarantees `v.validator \in Validators` (specs/tla/alpenglow/Messages.tla:54), ensuring well-typed extraction.
  - Whitepaper linkage: Definition 12 prescribes storage/multiplicity that leads to “count once” semantics; certificate aggregation should count stake of each validator at most once (alpenglow-whitepaper.md:513, alpenglow-whitepaper.md:554).

- Stake aggregation from votes
  - `StakeFromVotes(votes) == CalculateStake(UniqueValidators(votes))` (specs/tla/alpenglow/Certificates.tla:64–65) sums stake over the deduplicated validators using `StakeMap`. Since `ASSUME StakeMap \in [Validators -> Nat \ {0}]` (specs/tla/alpenglow/Certificates.tla:23), every validator has positive stake and the domain matches `Validators`.
  - `CalculateStake` and `TotalStake` are defined via structural sums over `StakeMap` (specs/tla/alpenglow/Certificates.tla:38, specs/tla/alpenglow/Certificates.tla:49), so there is no double-counting or ambiguity. Intersecting with `DOMAIN StakeMap` is a defensive guard; by assumption the domain is `Validators`.
  - Whitepaper linkage: Table 6 defines certificate conditions in terms of cumulative stake Σ of aggregated votes (alpenglow-whitepaper.md:507). This operator realizes Σ accurately and with the “count once” rule.

- Threshold comparison without division
  - `MeetsThreshold(stake, thresholdPercent) == stake * 100 >= TotalStake * thresholdPercent` (specs/tla/alpenglow/Certificates.tla:68–69) encodes ≥X% as an integer inequality, avoiding division and rounding concerns in TLA+.
  - With `Validators # {}` (specs/tla/alpenglow/Messages.tla:24) and positive stake (specs/tla/alpenglow/Certificates.tla:23), `TotalStake > 0` and threshold checks are meaningful.
  - Whitepaper linkage: Thresholds 80%/60% from Definition 11/Table 6 (alpenglow-whitepaper.md:501–505) are realized by passing 80 or 60 for `thresholdPercent`. The monotonicity implied by 80% ≥ 60% underpins “fast implies notarization” (alpenglow-whitepaper.md:534), which the module also encodes elsewhere.

- Context of use
  - Call sites filter `votes` to a single slot and intended vote types before applying `StakeFromVotes` (e.g., `relevantVotes` in `CanCreate*` predicates: specs/tla/alpenglow/Certificates.tla:83, 98, 112, 126, 140). This ensures “count once per slot” is applied exactly where intended by the paper.
  - Pool/multiplicity in `VoteStorage` additionally enforces Definition 12 at ingestion (one initial vote per slot, fallback caps), complementing the deduplication here.

**Conclusion**

- The three operators faithfully implement the whitepaper’s stake aggregation and threshold requirements:
  - UniqueValidators matches the “count once per slot” abstraction.
  - StakeFromVotes correctly computes Σ over unique validators.
  - MeetsThreshold implements ≥X% checks consistent with Table 6.
- Dependencies (`StakeMap`, `TotalStake`, `CalculateStake`) and typing assumptions guarantee well-defined behavior and exclude degenerate cases (e.g., zero total stake).
- Net assessment: Correct and complete with respect to Definition 11, Definition 12, and Table 6.

**Open Questions / Concerns**

- Slot scoping is by convention at call sites. `UniqueValidators`/`StakeFromVotes` are generic; correctness depends on callers filtering `votes` to a single slot. Current usages do this correctly, but misuse elsewhere could violate the intended per-slot semantics.
- `thresholdPercent` has no explicit type or bound in this operator. Passing values outside `[0, 100]` would still produce a boolean, which may be undesirable in proofs.
- Summations are defined recursively; TLAPS obligations (if any) are not included here. If mechanized proofs are planned, auxiliary lemmas about `CalculateStake`/`TotalStake` monotonicity could help.

**Suggestions for Improvement**

- Add a guard or type assertion for `thresholdPercent`:
  - e.g., `\* ASSUME ThresholdPercent \in {20,40,60,80}` or `thresholdPercent \in 0..100` where appropriate.
- Provide a slot-scoped helper to reduce misuse risk:
  - `StakeFromSlotVotes(votes, slot) == StakeFromVotes({v \in votes : v.slot = slot})`
  - Use this in `CanCreate*` to make slot scoping explicit.
- Document explicitly in the comment for `UniqueValidators` that callers must pass slot-filtered votes; the current call sites do, but the hint improves readability.
- Optional: add an invariant exercising “fast implies notarization” via monotonicity of `MeetsThreshold` and `StakeFromVotes` (the module already includes a related implication for certificates; keeping a direct note next to these operators can aid readers).

