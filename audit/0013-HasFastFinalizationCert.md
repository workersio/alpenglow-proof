# Audit: HasFastFinalizationCert(pool, slot, blockHash)

1. Code Under Audit

```
HasFastFinalizationCert(pool, slot, blockHash) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = "FastFinalizationCert"
        /\ cert.blockHash = blockHash
```

Source: specs/tla/alpenglow/VoteStorage.tla:238

2. Whitepaper Sections and References

- Table 6 (Certificate messages): Fast-Finalization Cert — NotarVote — Σ ≥ 80%
  - alpenglow-whitepaper.md:501
- Definition 13 (Pool — certificates: generate/store/broadcast; uniqueness per type/block/slot)
  - alpenglow-whitepaper.md:520
- Definition 14 (Finalization): fast path — “If a fast-finalization certificate on block b is in Pool, the block b is finalized.”
  - alpenglow-whitepaper.md:536, alpenglow-whitepaper.md:539
- Repair/bootstrapping context: nodes act on presence of (fast) finalization or notarization certificates to retrieve blocks
  - alpenglow-whitepaper.md:1229

3. Reasoning and Alignment with the Whitepaper

- Intended semantics
  - The predicate should be true exactly when the local Pool contains a fast-finalization certificate for block `blockHash` in the given `slot`. This is the guard the whitepaper uses in Definition 14 (“fast-finalization certificate on block b is in Pool”).
- Data model and storage discipline
  - Pool organizes certificates by slot: `pool.certificates: [Slots -> SUBSET Certificate]` (VoteStorage.tla). Certificates are inserted only via `StoreCertificate`, which writes into the bucket indexed by `cert.slot` and requires `IsValidCertificate(cert)`.
  - Certificate structure and types come from Messages.tla (`CertificateType` includes `"FastFinalizationCert"`; `Certificate` carries `slot`, `blockHash`). `IsValidCertificate` (Certificates.tla) ensures type-correct fields and threshold checks per Table 6.
  - Uniqueness/coherence: `CanStoreCertificate` (VoteStorage.tla) enforces at most one certificate of each type per slot/block and requires that all notar-related types {Notarization, NotarFallback, FastFinalization} in a slot agree on the same `blockHash`.
- Predicate correctness
  - Enumerating `pool.certificates[slot]` and checking `cert.type = "FastFinalizationCert" /\ cert.blockHash = blockHash` captures exactly “Pool holds a fast-finalization certificate for block b.” Explicit `cert.slot = slot` is redundant because the bucket selection uses `slot` and insertion uses `cert.slot` as the index.
- Usage sites (consistency with paper)
  - Finalization guard (fast path): MainProtocol.FinalizeBlock uses `HasFastFinalizationCert(pool, slot, block.hash)` per Definition 14.
  - Repair trigger: MainProtocol.NeedsBlockRepair includes this predicate, matching the bootstrapping/repair narrative (nodes can locate the block to retrieve when such a certificate is observed).
- Cross-module references relevant to this predicate
  - Messages.tla: Certificate types/record (CertificateType, Certificate).
  - Certificates.tla: `IsValidCertificate`, threshold parameters (80/60), and creation helpers (`CreateFastFinalizationCert`).
  - VoteStorage.tla: `PoolState`, `CanStoreCertificate`, `StoreCertificate`, and related invariants (`CertificateUniqueness`).
  - MainProtocol.tla: `FinalizeBlock`, `NeedsBlockRepair` use this predicate in alignment with Definition 14 and repair guidance.

4. Conclusion of the Audit

- The predicate precisely formalizes the whitepaper’s requirement: it is true iff the Pool contains a fast-finalization certificate for the specified block in the given slot. Given the storage and validation rules, this implies the 80% threshold was met on NotarVote for that block (Table 6) and that the block should be finalized per Definition 14.
- The definition is correct, minimal, and consistent with surrounding invariants (uniqueness and cross-type coherence). It aligns with how the protocol uses fast-finalization in finalization and repair logic.

5. Open Questions or Concerns

- Implicit slot equality. The predicate relies on the storage discipline that `pool.certificates[slot]` only contains certificates with `c.slot = slot`. This holds given current insertion paths, but it is not stated as an explicit invariant. Adding a bucket–slot consistency invariant would make this reliance explicit and tool-checkable.
- Defensive validity. The predicate assumes certificates in the Pool are valid because `StoreCertificate` enforces `IsValidCertificate`. If future code paths were to mutate `pool.certificates` directly, this assumption could be violated (no such path exists today).

6. Suggestions for Improvement

- Add a pool invariant documenting bucket–slot consistency for readability and robustness:
  - `BucketSlotConsistency(pool) == \A s \in Slots : \A c \in pool.certificates[s] : c.slot = s`.
  - Consider asserting it alongside `PoolTypeOK` and `CertificateUniqueness`.
- Optional readability tweak (not required for correctness): inline the redundant slot check for symmetry with other predicates:
  - `... /\ cert.slot = slot`.
- Comment the trust boundary near the certificate queries: note that validity is enforced on store via `IsValidCertificate`, so `Has*Cert` predicates can assume well-formed entries.

