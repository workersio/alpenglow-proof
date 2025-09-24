# Audit: `CanCreateFastFinalizationCert`

## 1. Code Under Audit

```tla
CanCreateFastFinalizationCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \\in votes : 
        /\ v.type = "NotarVote"
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 80)
```

Reference implementation in repo: `specs/tla/alpenglow/Certificates.tla:83`.

## 2. Whitepaper Mapping

- Voting and certificate message taxonomy: `alpenglow-whitepaper.md:478` (Definition 11), `alpenglow-whitepaper.md:501`–`alpenglow-whitepaper.md:507` (Table 6).
- Fast-Finalization certificate requires NotarVote with ≥80% stake: `alpenglow-whitepaper.md:501` (row: Fast‑Finalization Cert.).
- Count-once-per-slot stake aggregation (Pool storage rules): `alpenglow-whitepaper.md:513` (Definition 12).
- Implication: Fast‑Finalization implies Notarization (80% > 60%): `alpenglow-whitepaper.md:534`.

Relevant TLA+ definitions this operator depends on:
- `StakeFromVotes` and `MeetsThreshold`: `specs/tla/alpenglow/Certificates.tla:64`, `specs/tla/alpenglow/Certificates.tla:68`.
- Vote record shape and types (including `NotarVote`): `specs/tla/alpenglow/Messages.tla:29`, `specs/tla/alpenglow/Messages.tla:46`.
- Usage in certificate generation: `specs/tla/alpenglow/VoteStorage.tla:185`–`specs/tla/alpenglow/VoteStorage.tla:193`.

## 3. Reasoning vs Whitepaper

- The operator selects `relevantVotes` as exactly the notarization votes for the given `slot` and `blockHash`, i.e., only `NotarVote` messages. This matches Table 6’s first row requiring NotarVote for fast finalization (`alpenglow-whitepaper.md:501`).
- It then computes stake as `StakeFromVotes(relevantVotes)`. In `Certificates.tla`, stake is derived from unique validators: `StakeFromVotes(votes) == CalculateStake(UniqueValidators(votes))` (`specs/tla/alpenglow/Certificates.tla:64`). This encodes Definition 12’s “count once per slot” rule (`alpenglow-whitepaper.md:513`).
- Threshold check `MeetsThreshold(stake, 80)` implements “≥80% of total stake” using integer arithmetic: `stake * 100 >= TotalStake * 80` (`specs/tla/alpenglow/Certificates.tla:68`). This avoids rounding issues and aligns with the whitepaper’s percentage semantics.
- Integration context: When fast finalization condition holds, the pool creates a FastFinalizationCert and, by design, also creates Notarization and Notar‑Fallback certificates for the same block (`specs/tla/alpenglow/VoteStorage.tla:185`–`specs/tla/alpenglow/VoteStorage.tla:193`). This mirrors the whitepaper’s implication that 80% implies the 60% certificates also exist (`alpenglow-whitepaper.md:534`).

## 4. Conclusion

- The operator is correct and faithful to the whitepaper:
  - Vote type restriction: only `NotarVote` is counted (Table 6 requirement).
  - Stake aggregation: counts each validator at most once per slot (Definition 12).
  - Threshold: checks ≥80% of total stake (Table 6 fast path).
- The surrounding modules consistently enforce prerequisites and implications:
  - Vote structure and validity are defined in `Messages.tla`.
  - Pool storage rules prevent double initial voting and ensure per‑validator uniqueness (Definition 12 enforced in `VoteStorage.tla`).
  - Certificate generation creates accompanying 60% certificates when the 80% condition holds, matching the whitepaper implication.

Overall, the abstraction captured by `CanCreateFastFinalizationCert` precisely matches the whitepaper’s fast‑finalization criterion.

## 5. Open Questions / Concerns

- Source of `votes` argument: The operator assumes `votes` come from Pool and thus already respect Definition 12 multiplicity rules. This is true in current usage (`GenerateCertificate` passes `GetVotesForSlot(pool, slot)`), but worth documenting at the operator’s call sites.
- Membership/stake dynamics: `TotalStake` is computed from constant `StakeMap` (positive stake per validator). If validator sets or stakes change across slots, this module treats them as fixed during analysis. If dynamic stake is intended, consider clarifying temporal scope in comments.
- Ambiguity in external filtering: The operator directly filters by fields; alternative helpers like `GetVotesForBlock` from `Messages.tla` include fallback votes by design, so are not suitable here. The current explicit filter is correct but could invite accidental misuse elsewhere.

## 6. Suggestions for Improvement

- Add named constants for thresholds to avoid magic numbers and ease cross‑audits:
  - `FastFinalThreshold == 80` and `DefaultThreshold == 60`, referenced from all certificate predicates.
- Document preconditions at the operator level: “`votes` must be a Pool‑sourced set to ensure count‑once semantics,” even though `StakeFromVotes` is defensive against duplicates.
- Add a local sanity property near definitions: “Fast path excludes fallback votes” (e.g., a comment or lemma stating that all `cert.votes` in a `FastFinalizationCert` satisfy `v.type = "NotarVote"`). While `CreateFastFinalizationCert` already enforces this, an explicit property can help readers.

