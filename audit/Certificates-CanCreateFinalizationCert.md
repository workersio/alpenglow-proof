# Audit: `CanCreateFinalizationCert`

## 1. Code Under Audit

```tla
CanCreateFinalizationCert(votes, slot) ==
    LET relevantVotes == {v \\in votes :
        /\ v.type = "FinalVote"
        /\ v.slot = slot}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 60)
```

Reference implementation in repo: `specs/tla/alpenglow/Certificates.tla:138`.

## 2. Whitepaper Mapping

- Definition 11 (messages): `alpenglow-whitepaper.md:478` (Tables 5 & 6)
  - Finalization vote: `FinalVote(s)` — `alpenglow-whitepaper.md:495` (Table 5)
  - Finalization certificate: vote type `FinalVote`, threshold `Σ ≥ 60%` — `alpenglow-whitepaper.md:505` (Table 6)
- Count-once-per-slot stake accounting: `alpenglow-whitepaper.md:513` (Definition 12)
- Finalization modes (fast vs slow): `alpenglow-whitepaper.md:536` (Definition 14)
  - Slow path: FinalizationCert(s) + NotarizationCert(s, b) → finalize `b`

Related TLA+ dependencies and usage:
- Stake and threshold helpers: `specs/tla/alpenglow/Certificates.tla:64` (StakeFromVotes), `specs/tla/alpenglow/Certificates.tla:68` (MeetsThreshold)
- Vote schema and `FinalVote`: `specs/tla/alpenglow/Messages.tla:29`, `specs/tla/alpenglow/Messages.tla:95`
- Certificate construction and queries: `specs/tla/alpenglow/Certificates.tla:178`, `specs/tla/alpenglow/VoteStorage.tla:204`, `specs/tla/alpenglow/VoteStorage.tla:237`
- Protocol use of slow-path finalization: `specs/tla/alpenglow/MainProtocol.tla:248`–`specs/tla/alpenglow/MainProtocol.tla:262`

## 3. Reasoning vs Whitepaper

- Vote selection: `relevantVotes` filters exactly `FinalVote` messages for the given `slot`. This matches Table 6’s requirement that a Finalization Certificate aggregates FinalVote only.
- Stake aggregation: `StakeFromVotes(relevantVotes)` uses unique validators (via `UniqueValidators`) to respect the “count once per slot” rule of Definition 12. Thus multiple FinalVote messages by the same validator in the same slot cannot inflate stake.
- Threshold check: `MeetsThreshold(..., 60)` implements `Σ ≥ 60%` using integer arithmetic (`stake * 100 ≥ TotalStake * 60`), consistent with the percentage semantics in the whitepaper and avoiding rounding errors.
- Abstraction alignment: The operator purely states the condition for assembling a Finalization Certificate; it intentionally carries no block hash because finalization in the slow path combines a slot‑level certificate (FinalizationCert(s)) with a notarization certificate binding the block (NotarizationCert(s, b)), per Definition 14.
- Integration: In `VoteStorage.GenerateCertificate`, if `CanCreateFinalizationCert` holds, the pool creates `CreateFinalizationCert(votes, slot)` and stores at most one per slot (`VoteStorage.tla:115`–`116`). This matches the whitepaper’s uniqueness intent for certificates per slot/type.

## 4. Conclusion

- The operator is correct and faithful to the whitepaper:
  - Aggregates only `FinalVote` messages for the slot (Table 6).
  - Counts stake once per validator per slot (Definition 12).
  - Enforces the `≥ 60%` threshold (Table 6).
  - Abstractly aligns with Definition 14’s slow-path finalization that pairs this slot‑level certificate with a block‑bound notarization certificate to finalize a specific block.

## 5. Open Questions / Concerns

- Source of `votes`: The predicate assumes `votes` are the pool’s per‑slot view, which respects Definition 12 multiplicity rules. Current call sites honor this (`GenerateCertificate` passes votes for the slot), but documenting this expectation helps prevent misuse.
- Dynamic validator set or stake: `TotalStake` comes from constant `StakeMap`. If stake or membership varies with time, clarify whether `StakeMap` is intended time‑invariant within the modeled horizon, or parameterized per epoch/slot.
- Uniqueness across network: `CanStoreCertificate` ensures at most one FinalizationCert per slot per pool instance. Global uniqueness depends on protocol safety (e.g., no conflicting notarizations) rather than this operator. That is correct by abstraction, but worth noting for readers.

## 6. Suggestions for Improvement

- Use named constants for thresholds (e.g., `DefaultThreshold == 60`) to avoid magic numbers and to tie all uses to a single definition.
- Add a brief note near `CreateFinalizationCert` or here that FinalizationCert is intentionally slot‑only (blockHash = NoBlock) because block binding is provided by the notarization certificate in the slow path per Definition 14.
- Optionally add a lemma: if `HasFinalizationCert(s)` and `HasNotarizationCert(s, b)` then `Finalize(b)` holds (echoing the property already used in `MainProtocol.tla:260`–`262`), to make the connection explicit in the certificate module.

