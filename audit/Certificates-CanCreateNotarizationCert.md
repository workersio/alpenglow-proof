# Audit: `CanCreateNotarizationCert`

## 1. Code Under Audit

```tla
CanCreateNotarizationCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes :
        /\ v.type = "NotarVote"
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 60)
```

Reference implementation in repo: `specs/tla/alpenglow/Certificates.tla:97`.

## 2. Whitepaper Mapping

- Voting/certificate taxonomy: `alpenglow-whitepaper.md:478` (Definition 11), `alpenglow-whitepaper.md:507` (Table 6 header and description).
- Table 6, Notarization Cert row: Aggregated votes = NotarVote, condition = Σ ≥ 60% (`alpenglow-whitepaper.md:507`).
- Count-once-per-slot rule (Pool storage semantics): `alpenglow-whitepaper.md:513` (Definition 12).
- Implication relationship (80% implies 60% certificates also exist): `alpenglow-whitepaper.md:534`.

Related TLA+ references used by this operator:
- Stake aggregation and threshold checks:
  - `UniqueValidators(votes)`: `specs/tla/alpenglow/Certificates.tla:60`.
  - `StakeFromVotes(votes) == CalculateStake(UniqueValidators(votes))`: `specs/tla/alpenglow/Certificates.tla:64`–`specs/tla/alpenglow/Certificates.tla:65`.
  - `MeetsThreshold(stake, thresholdPercent) == stake * 100 >= TotalStake * thresholdPercent`: `specs/tla/alpenglow/Certificates.tla:68`–`specs/tla/alpenglow/Certificates.tla:69`.
  - `TotalStake`/`StakeMap` assumptions: `specs/tla/alpenglow/Certificates.tla:19`, `specs/tla/alpenglow/Certificates.tla:22`–`specs/tla/alpenglow/Certificates.tla:23`.
- Vote types and structure (for `v.type`, `v.slot`, `v.blockHash`): `specs/tla/alpenglow/Messages.tla:43`, `specs/tla/alpenglow/Messages.tla:52`–`specs/tla/alpenglow/Messages.tla:57`.
- How it is used in certificate creation: `specs/tla/alpenglow/VoteStorage.tla:185`–`specs/tla/alpenglow/VoteStorage.tla:204`.

## 3. Reasoning vs Whitepaper

- Vote selection aligns with Table 6: `relevantVotes` are exactly the notarization votes for the target `(slot, blockHash)`, restricted to `v.type = "NotarVote"`. Table 6 specifies Notarization Cert uses NotarVote only with a ≥60% condition (`alpenglow-whitepaper.md:507`).
- Count-once-per-slot is enforced via aggregation over unique validators: `StakeFromVotes(relevantVotes)` reduces to `CalculateStake(UniqueValidators(relevantVotes))` (`specs/tla/alpenglow/Certificates.tla:64`). This is the specification-level realization of Definition 12’s count-once rule (`alpenglow-whitepaper.md:513`). Even if a validator submitted multiple identical NotarVote messages, stake is still counted once.
- Threshold semantics match percentages of total stake: `MeetsThreshold(stake, 60)` checks `stake * 100 >= TotalStake * 60` (`specs/tla/alpenglow/Certificates.tla:68`). `TotalStake` is the sum over `StakeMap`, whose domain is exactly `Validators` and is non-empty and strictly positive by assumptions (cf. `specs/tla/alpenglow/Messages.tla:23`–`specs/tla/alpenglow/Messages.tla:27`, `specs/tla/alpenglow/Certificates.tla:22`–`specs/tla/alpenglow/Certificates.tla:23`). This matches Table 6’s “Σ ≥ 60% of stake” claim.
- Integration is consistent with Pool rules and certificate creation:
  - `GenerateCertificate` in `VoteStorage.tla` applies this predicate to votes for the slot, producing the NotarizationCert when the condition holds, and ensuring the 80% path also yields 60% certificates as implied by the whitepaper (`specs/tla/alpenglow/VoteStorage.tla:185`–`specs/tla/alpenglow/VoteStorage.tla:204`, `alpenglow-whitepaper.md:534`).
  - Pool storage (Definition 12) prevents multiple initial votes per validator per slot, which is necessary for the uniqueness and safety lemmas that underpin notarization uniqueness.

## 4. Conclusion of the Audit

- The operator `CanCreateNotarizationCert` correctly and completely captures the Notarization Certificate condition from the whitepaper (Table 6):
  - Filters exactly NotarVote for the `(slot, blockHash)` in question.
  - Sums stake over unique validators, implementing count-once-per-slot.
  - Checks a 60% threshold against the total system stake.
- The definitions it relies on (`StakeFromVotes`, `MeetsThreshold`, `UniqueValidators`, `TotalStake`) are correctly specified and consistent with the whitepaper’s abstractions.
- Its usage in `VoteStorage.tla` aligns with Definition 13’s rule to generate certificates “when enough votes are received,” and with the implication that 80% ⇒ 60% certificates exist for the same block.

Result: Faithful to the whitepaper; no specification-level mismatches found.

## 5. Open Questions / Concerns

- Provenance of `votes`: The predicate is correct for any set of well-formed votes, but to ensure count-once semantics per slot, callers should pass Pool-sourced votes (as done via `GetVotesForSlot` in `VoteStorage.tla`). Suggest documenting this precondition.
- Explicit type discipline: The predicate does not itself assert `votes \subseteq Vote` or `blockHash \in BlockHashes`. These are enforced when constructing/validating certificates elsewhere (e.g., `IsValidCertificate`), but a brief note in comments could prevent accidental misuse in isolation.
- Threshold constants: The literal `60` appears here and at other call sites. Using named constants would reduce drift if thresholds evolve or need centralization.
- Dynamic stake epochs: The model assumes fixed `StakeMap` over the analysis horizon. If stake changes are intended between slots/epochs, consider clarifying the temporal scope of `TotalStake` (outside this operator’s remit, but useful context).

## 6. Suggestions for Improvement

- Introduce named parameters for thresholds:
  - `DefaultThreshold == 60`, `FastThreshold == 80`, and replace numeric literals across predicates.
- Add a lemma to tie fast and standard notarization creation conditions for readability (the certificate-level implication already exists):
  - `\A votes, s, b : CanCreateFastFinalizationCert(votes, s, b) => CanCreateNotarizationCert(votes, s, b)`.
- Add a small comment to `CanCreateNotarizationCert` stating “`votes` are Pool-sourced” to signal the reliance on Definition 12 without re-enforcing it locally.
- Optionally, include a helper `GetNotarVotesForBlock(votes, slot, blockHash)` to centralize the filtering logic (already mirrored in `Messages.tla` helpers for other queries), reducing duplication and avoiding accidental inclusion of fallback votes.

