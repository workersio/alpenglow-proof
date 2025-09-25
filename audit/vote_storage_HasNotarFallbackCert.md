# Audit: VoteStorage.HasNotarFallbackCert

1. Code Audited

```tla
HasNotarFallbackCert(pool, slot, blockHash) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = "NotarFallbackCert"
        /\ cert.blockHash = blockHash
```

2. Whitepaper Sections and References

- Section 2.4 (Votes & Certificates): Table 6 — Notar-Fallback Certificate defined as aggregation of NotarVote or NotarFallbackVote with Σ ≥ 60%.
- Section 2.5 (Pool):
  - Definition 12 (storing votes): Pool stores votes with multiplicity rules; stake counted once per slot.
  - Definition 13 (certificates): Pool generates, stores, and broadcasts certificates; stores a single certificate of each type per block/slot. Note: fast ⇒ notar ⇒ fallback.
- Section 2.5 (Definition 15, Pool events):
  - ParentReady(s, hash(b)) is emitted when Pool holds a notarization or notar-fallback certificate for a previous block b and skip certificates for slots between slot(b) and s.
- Section 2.5 (Definition 16, fallback events): SafeToNotar requires, if not the first slot of the leader window, the Pool to contain the notar-fallback certificate for the parent.

3. Reasoning (Spec vs. Whitepaper)

- Intent: Predicate answers the question “Does this local Pool hold a notar-fallback certificate for block ‘blockHash’ in slot ‘slot’?”
- Pool typing/shape: `pool.certificates` is a mapping from `Slots` to subsets of `Certificate` (VoteStorage.tla, PoolState). Certificates (Messages.tla) have fields `type`, `slot`, `blockHash`, `votes` and include a `"NotarFallbackCert"` variant.
- Correctness of fields: Notar-related certificates carry a concrete `blockHash ∈ BlockHashes` (Certificates.tla: IsValidCertificate requires block-scoped types to have a block hash in domain and meet threshold). Skip/Finalization certificates use `NoBlock`; this predicate correctly ignores them by matching on type and equating the block hash.
- Alignment to Table 6: Presence of a `"NotarFallbackCert"` corresponds exactly to “Pool holds a notar-fallback certificate for block b” in §2.5 events, and to the implied generation rule from §2.4/§2.5 (Def. 13).
- Use-site semantics (cross-check):
  - ParentReady: Code elsewhere gates ParentReady on `(HasNotarizationCert ∨ HasNotarFallbackCert)` for a previous block, matching Definition 15.
  - SafeToNotar: Code requires, for non-first slots, the notar-fallback certificate for the parent (specifically fallback, not notar), matching the explicit requirement in Definition 16.

4. Conclusion

- The predicate is a faithful, minimal abstraction of “Pool holds a notar-fallback certificate for (slot, blockHash)” as specified by the whitepaper. It matches the Pool’s storage model (one certificate per type per block/slot) and integrates correctly with event gating in Definition 15 and Definition 16.
- No additional filtering is required inside the predicate because Pool storage already enforces certificate validity (`IsValidCertificate`) and uniqueness/cross-type coherence (VoteStorage.tla `CanStoreCertificate`), and global invariants check for conflicts.

5. Open Questions / Concerns

- None blocking. Noted assumptions:
  - Predicate relies on Pool invariants for correctness (e.g., that stored certificates are valid and non-conflicting). If callers use untyped Pools, extra guards would be needed; the current model types `PoolState` adequately.
  - In pathological states (violating invariants), the existential could match a conflicting fallback certificate. The model includes invariants (`AllCertificatesValid`, `NoConflictingCertificates`, `SkipVsBlockCertExclusion`) to preclude such states.

6. Suggestions for Improvement

- Optional type-assertion helper: add light-weight typing lemmas near callers rather than inside this predicate, e.g., `slot ∈ Slots`, `blockHash ∈ BlockHashes`, to aid proof obligations without cluttering the core predicate.
- Optional API consolidation: introduce a generic `HasBlockCertOfType(pool, slot, blockHash, type)` to DRY the family of `Has*Cert` predicates, while keeping the current specialized names as wrappers for readability.

Prepared by: TLA+ audit of `HasNotarFallbackCert` in VoteStorage.tla (Pool certificate queries).

