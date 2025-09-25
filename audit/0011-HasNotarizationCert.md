# Audit: HasNotarizationCert(pool, slot, blockHash)

1. Code Under Audit

```
HasNotarizationCert(pool, slot, blockHash) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = "NotarizationCert"
        /\ cert.blockHash = blockHash
```

Source: `specs/tla/alpenglow/VoteStorage.tla:221`

2. Whitepaper References Represented

- 2.5 Pool — certificates and events
  - Definition 13 (Certificates): `alpenglow-whitepaper.md:520–534`
    - “A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool.”
  - Events (Definition 15): `alpenglow-whitepaper.md:543–546`
    - BlockNotarized(slot(b), hash(b)): “Pool holds a notarization certificate for block b.”
    - ParentReady(s, hash(b)): requires a notarization or notar-fallback certificate for a previous block.
- Table 6 (Certificate messages): Notarization Certificate row `alpenglow-whitepaper.md:502`, table header `alpenglow-whitepaper.md:507`.

3. Reasoning and Alignment With Whitepaper

- Intended meaning. The predicate should be true exactly when the local Pool contains a notarization certificate for block `blockHash` in the given `slot`, matching Definition 15’s “Pool holds a notarization certificate for block b.”
- Data model match.
  - Pool structure: `pool.certificates: [Slots -> SUBSET Certificate]` (VoteStorage) organizes certificates by slot bucket; see `specs/tla/alpenglow/VoteStorage.tla:24` and initialization `:30`.
  - Certificate records carry `type`, `slot`, and `blockHash`; see `specs/tla/alpenglow/Messages.tla:142` (CertificateType) and `:151` (Certificate).
  - Certificates are created with matching `(slot, blockHash)`; see `specs/tla/alpenglow/Certificates.tla:223` (CreateNotarizationCert) and validated by `IsValidCertificate` `:268`.
- Pool insertion discipline enforces correctness of the bucket.
  - Store path writes to the bucket indexed by `cert.slot`: `specs/tla/alpenglow/VoteStorage.tla:130` (StoreCertificate) after `CanStoreCertificate` gate `:109`.
  - Uniqueness and cross-type coherence for notar-related certs are enforced by `CanStoreCertificate` (same `blockHash` across {Notarization, NotarFallback, FastFinalization}).
- Predicate semantics. The existential over `pool.certificates[slot]` with constraints `type = "NotarizationCert"` and `blockHash = blockHash` captures exactly “Pool holds a notarization certificate for block b.” Slot matching is implicit by reading from the `slot` bucket.
- Usage sites align with Definition 15 events:
  - `ShouldEmitBlockNotarized` is exactly `HasNotarizationCert(...)` (`specs/tla/alpenglow/VoteStorage.tla:257`).
  - `ShouldEmitParentReady` accepts either notarization or notar-fallback for the parent (`specs/tla/alpenglow/VoteStorage.tla:268`).

4. Conclusion

- The definition correctly formalizes the whitepaper’s event guard “Pool holds a notarization certificate for block b” (Definition 15) by checking for an existing `NotarizationCert` with the given `blockHash` in the `slot`’s certificate set.
- Consistency with Definition 13 is maintained indirectly: certificates are only inserted via `StoreCertificate`, which validates and buckets certificates by their `slot`, and enforces uniqueness and cross-type coherence.
- Overall, the predicate is correct and minimal, and its usage in event guards matches the whitepaper.

5. Open Questions / Concerns

- Bucket/slot consistency is relied upon but not stated here. While `StoreCertificate` inserts into the `cert.slot` bucket, there is no separate invariant tying every `c \in pool.certificates[s]` to `c.slot = s`. This is standard in TLA+, but making it explicit as an invariant would improve robustness against accidental alternative writes.
- Defensive validity check. `HasNotarizationCert` assumes stored certs are valid (because `StoreCertificate` requires `IsValidCertificate`). If other paths ever mutate `pool.certificates` directly (e.g., future extensions), the predicate might accept malformed records. Today this is not the case.

6. Suggestions for Improvement

- Add an explicit pool invariant documenting bucket-slot consistency for readability and tool-checking:
  - Example: `BucketSlotConsistency(pool) == \A s \in Slots : \A c \in pool.certificates[s] : c.slot = s`.
  - Place alongside existing invariants (`PoolTypeOK`, `CertificateUniqueness`) in `VoteStorage.tla`.
- Optional readability tweak (not required for correctness): inline the slot equality in the predicate, even though it is implied by the bucket:
  - `... /\ cert.slot = slot`.
- Consider documenting in a comment near `HasNotarizationCert` that certificate validity is ensured by the storage path (`StoreCertificate`) to make the trust boundary explicit.

7. Cross-Module References (for completeness)

- Pool structure and guards: `specs/tla/alpenglow/VoteStorage.tla:24, 109, 130`.
- Certificate creation/validation: `specs/tla/alpenglow/Certificates.tla:223, 268`.
- Certificate types/record: `specs/tla/alpenglow/Messages.tla:142, 151`.
- Event guards using this predicate: `specs/tla/alpenglow/VoteStorage.tla:257, 268`.

