# Audit: CanCreateSkipCert

## 1. Code Under Audit

```
CanCreateSkipCert(votes, slot) ==
    LET relevantVotes == {v \in votes :
        /\ v.type \in {"SkipVote", "SkipFallbackVote"}
        /\ v.slot = slot}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 60)
```

## 2. Whitepaper Sections and References

- Definition 11 (messages) and Table 6 (certificate thresholds): `alpenglow-whitepaper.md:478`, `alpenglow-whitepaper.md:499`–`alpenglow-whitepaper.md:507`.
  - Table 6 (row “Skip Cert.”): Aggregated votes = SkipVote or SkipFallbackVote; Condition Σ ≥ 60%: `alpenglow-whitepaper.md:504`–`alpenglow-whitepaper.md:507`.
- Definition 12 (storing votes, count-once-per-slot semantics): `alpenglow-whitepaper.md:513`–`alpenglow-whitepaper.md:519`.

## 3. Reasoning and Mapping to Whitepaper

- Vote types filtered
  - The predicate includes both `SkipVote` and `SkipFallbackVote` and restricts them to the same `slot` via `v.slot = slot`.
  - This matches Table 6 (Skip Cert uses SkipVote or SkipFallbackVote): `alpenglow-whitepaper.md:504`.
  - Vote type definitions are consistent with the message module: `specs/tla/alpenglow/Messages.tla:43`–`specs/tla/alpenglow/Messages.tla:49`, constructors at `specs/tla/alpenglow/Messages.tla:80`–`specs/tla/alpenglow/Messages.tla:93`.

- Stake aggregation and “count once per slot”
  - Stake is computed as `StakeFromVotes(relevantVotes)`, which reduces votes to unique validators before summing stake, preventing double counting if a validator sent both a `SkipVote` and a `SkipFallbackVote` for the same slot.
  - Implementations:
    - `UniqueValidators(votes)`: `specs/tla/alpenglow/Certificates.tla:60`–`specs/tla/alpenglow/Certificates.tla:61`.
    - `StakeFromVotes(votes)`: `specs/tla/alpenglow/Certificates.tla:64`–`specs/tla/alpenglow/Certificates.tla:65`.
    - `CalculateStake(validatorSet)`: `specs/tla/alpenglow/Certificates.tla:50`–`specs/tla/alpenglow/Certificates.tla:57`.
  - This matches Definition 12’s “count-once-per-slot” intent for certificate aggregation: `alpenglow-whitepaper.md:513`–`alpenglow-whitepaper.md:519`.

- Threshold check at 60%
  - `MeetsThreshold(stake, 60)` checks `stake * 100 >= TotalStake * 60`: `specs/tla/alpenglow/Certificates.tla:68`–`specs/tla/alpenglow/Certificates.tla:69`.
  - This implements Table 6’s Σ ≥ 60% requirement for Skip certificates: `alpenglow-whitepaper.md:504`–`alpenglow-whitepaper.md:507`.
  - `TotalStake` is defined over all validators with positive stake (assumption on `StakeMap`): `specs/tla/alpenglow/Certificates.tla:16`–`specs/tla/alpenglow/Certificates.tla:31`.

- Integration context (non-normative for this check, but relevant)
  - The creation function is used by the aggregator when generating certificates: `specs/tla/alpenglow/VoteStorage.tla:201`–`specs/tla/alpenglow/VoteStorage.tla:212`.
  - The constructed Skip certificate carries `NoBlock`, consistent with skip semantics: `specs/tla/alpenglow/Certificates.tla:170`–`specs/tla/alpenglow/Certificates.tla:176`.

## 4. Conclusion

The specification `CanCreateSkipCert` correctly implements the whitepaper’s Skip Certificate rule:
- It aggregates both Skip initial and Skip-fallback votes for the specified slot.
- It counts each validator at most once within the slot’s aggregation through `StakeFromVotes`/`UniqueValidators`, matching Definition 12’s intent.
- It enforces the 60% total stake threshold exactly as per Table 6.

Therefore, the abstraction is faithful to the whitepaper for the Skip Certificate creation condition.

## 5. Open Questions or Concerns

- Concurrent cert coexistence (spec-level vs. protocol-level):
  - This predicate alone doesn’t preclude a Skip certificate and a Notarization/Notar-Fallback certificate from being creatable in the same slot if both reach ≥60% via different coalitions.
  - The whitepaper proves such coexistence cannot arise among correct nodes under the given assumptions (e.g., byzantine stake < 20%, fallback gating), see arguments around mutual exclusion: `alpenglow-whitepaper.md:830`, `alpenglow-whitepaper.md:878`.
  - In the TLA spec, `GenerateCertificate` returns the union of all creatable certs for a slot (`specs/tla/alpenglow/VoteStorage.tla:189`–`specs/tla/alpenglow/VoteStorage.tla:212`), and storage uniqueness `CanStoreCertificate` does not explicitly forbid storing a Skip certificate alongside a Notarization/Notar-Fallback certificate (`specs/tla/alpenglow/VoteStorage.tla:168`–`specs/tla/alpenglow/VoteStorage.tla:185`).
  - This likely relies on other model dynamics (event guards, fallback conditions) and the whitepaper’s safety lemmas rather than a local guard here. Consider asserting this property as an invariant (see Suggestions).

- Glossary alignment: The code uses explicit type literals instead of helper predicates (e.g., `IsSkipVote`). This is purely stylistic but can affect readability.

## 6. Suggestions for Improvement

- Add an invariant capturing mutual exclusion for a slot:
  - “No slot has both a SkipCert and any of {NotarizationCert, NotarFallbackCert, FastFinalizationCert}.”
  - This mirrors whitepaper statements that in a given slot, notarization on one block excludes skip certificates (and vice versa) under the model assumptions.

- Optionally gate Skip certificate emission in the generator with a non-functional guard (documentation-only or assert) that no block certificate in the same slot has reached threshold, to surface modeling errors earlier.

- Minor readability change: replace the explicit type set with the helper predicate from `Messages.tla`:
  - `v.type ∈ {"SkipVote","SkipFallbackVote"}` → `IsSkipVote(v)` (`specs/tla/alpenglow/Messages.tla:114`–`specs/tla/alpenglow/Messages.tla:116`). Functionally identical; improves clarity.

Overall, the audited expression is correct and aligns with the whitepaper’s abstractions for Skip Certificate creation.

