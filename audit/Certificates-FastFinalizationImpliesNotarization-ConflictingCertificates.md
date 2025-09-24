# Audit: FastFinalizationImpliesNotarization and ConflictingCertificates

## 1. Code Under Audit

```
FastFinalizationImpliesNotarization(fastCert, notarCert) ==
    /\ fastCert.type = "FastFinalizationCert"
    /\ notarCert.type = "NotarizationCert"
    /\ fastCert.slot = notarCert.slot
    /\ fastCert.blockHash = notarCert.blockHash
    => notarCert.votes \subseteq fastCert.votes

\* Check if two certificates conflict (shouldn't happen!)
ConflictingCertificates(cert1, cert2) ==
    /\ cert1.slot = cert2.slot           \* Same slot
    /\ cert1.type = cert2.type           \* Same type
    /\ cert1.blockHash # cert2.blockHash \* Different blocks!
```

Context: These definitions live in `specs/tla/alpenglow/Certificates.tla:217` and `:225`. They operate over `Certificate` records defined in `specs/tla/alpenglow/Messages.tla` and are used alongside certificate creation/validation logic in `Certificates.tla` and storage rules in `specs/tla/alpenglow/VoteStorage.tla`.

## 2. Whitepaper Sections and References

- Voting/certificates overview and fast/slow thresholds: `alpenglow-whitepaper.md:476`–`:507` (Definition 11; Table 6). Key rows:
  - Fast-Finalization Cert: NotarVote, Σ ≥ 80% (`:501`)
  - Notarization Cert: NotarVote, Σ ≥ 60% (`:501`–`:507`)
- Pool certificate generation/storage rules: `alpenglow-whitepaper.md:520`–`:534` (Definition 13).
  - Single stored copy per type per slot/block: `:532`.
  - Implication note: fast cert ⇒ notarization cert ⇒ notar-fallback cert: `:534`.
- Uniqueness of notarized block per slot: `alpenglow-whitepaper.md:538`, `:851` (Lemma 23), `:855` (Lemma 24).
- Vote multiplicity constraint (one initial vote per slot): `alpenglow-whitepaper.md:820` (Lemma 20).

Related spec references for context:
- Certificate constructors and thresholds: `specs/tla/alpenglow/Certificates.tla:86`–`:172`.
- Certificate creation bundle (creates fast + notar + fallback together when 80% holds): `specs/tla/alpenglow/VoteStorage.tla:152`–`:179`.
- Pool uniqueness across notarization/fast/fallback (same blockHash per slot): `specs/tla/alpenglow/VoteStorage.tla:98`–`:117`.
- Prefer notarization for broadcast when multiple candidates exist: `specs/tla/alpenglow/MainProtocol.tla:224`–`:240`.
- Global notarization uniqueness invariant (cross-validator): `specs/tla/alpenglow/MainProtocol.tla:818`–`:836`.

## 3. Reasoning vs. Whitepaper Claims

### 3.1 FastFinalizationImpliesNotarization
- Intent: Capture a strengthened relationship between fast and notarization certificates for the same `(slot, blockHash)` by stating `notarCert.votes ⊆ fastCert.votes`.
- Whitepaper claim: Table 6 thresholds (80% vs 60%) and the note (`:534`) imply that any correct node that can generate a fast certificate also generates the notarization certificate for the same block and slot.
- Spec mechanics: When the fast threshold holds, `GenerateCertificate` constructs all three certificates (fast, notarization, notar-fallback) from the same local vote view `votes` at that moment (`specs/tla/alpenglow/VoteStorage.tla:165`–`:176`). The constructors for fast/notarization both include all NotarVote messages for the `(slot, blockHash)` (`Certificates.tla:140`–`:167`). Therefore, within a single pool view:
  - The two certificates’ `votes` sets are equal at creation time, hence the subset relation holds trivially.
  - If created at different times from different local `votes` snapshots, the pool stores exactly one per type per `(slot, blockHash)` (`VoteStorage.tla:98`–`:117`), so re-creation is blocked; the canonical stored pair still satisfies equality/subset.
- Conclusion: The predicate is a sound strengthening of the paper’s “fast ⇒ notarization exists” implication. It is consistent with Definition 13’s generation behavior and Table 6 thresholds. It implicitly presumes both certificates come from the same node’s pool or an equivalent view.

### 3.2 ConflictingCertificates
- Intent: Flag a conflict when two certificates have the same `slot` and `type` but different `blockHash`.
- Whitepaper claim: At most one block can be notarized in a given slot (Lemma 24, `:855`), and Definition 13 stores a single certificate per type per slot/block (`:532`). Moreover, `:538` references “the unique notarized block” in slot `s`.
- Spec mechanics:
  - Within a pool, `CanStoreCertificate` enforces cross-type consistency across the “NotarTypes” family: Notarization, NotarFallback, and FastFinalization certificates stored for a slot must all share the same `blockHash` (`VoteStorage.tla:103`–`:117`). This prevents cross-type conflicts for notar-like certificates.
  - The audited `ConflictingCertificates` predicate is a minimal structural check (same type/slot, different hash). It would not by itself detect cross-type conflicts (e.g., `NotarizationCert(b1)` vs `NotarFallbackCert(b2)`); however, those are prevented by the pool storage rule above and further guarded by the global cross-validator invariant `GlobalNotarizationUniqueness` (`MainProtocol.tla:818`–`:836`).
- Conclusion: The predicate matches a necessary subset of the paper’s uniqueness requirements. The full uniqueness intent is realized in the spec by a combination of storage rules (per-node) and a cross-validator invariant (global), aligned with Lemma 24.

## 4. Conclusion of the Audit
- FastFinalizationImpliesNotarization: Correct and faithful, and actually stronger than the paper’s implication. Under the spec’s constructors and generation bundling, `notarCert.votes ⊆ fastCert.votes` holds (indeed equality at creation). This accurately reflects Table 6 and the note at `alpenglow-whitepaper.md:534`.
- ConflictingCertificates: Correct as a basic conflict detector for same-type duplicates. Full safety against notar-related conflicts is achieved by `CanStoreCertificate`’s cross-type blockHash coherence and the `GlobalNotarizationUniqueness` invariant, matching Lemma 24.

## 5. Open Questions / Concerns
- Scope of subset relation: The `FastFinalizationImpliesNotarization` predicate is unscoped to a pool/view. Across different nodes or times, two certificates for the same `(slot, blockHash)` could have different `votes` sets. The property is intended for certificates produced from a consistent local view (as in the spec), but consider documenting that assumption.
- Cross-type conflict detection outside Pool: If `ConflictingCertificates` were applied to arbitrary certificate sets (e.g., raw network messages), it would not catch `NotarizationCert(b1)` vs `NotarFallbackCert(b2)` in the same slot. The spec presently relies on Pool storage rules and a global invariant instead; this should be explicit in comments near the predicate to avoid misuse.

## 6. Suggestions for Improvement
- Clarify scope in code comments for `FastFinalizationImpliesNotarization` to state it is intended for certificates produced under the same local vote view (or from the same pool).
- Optional strengthening: Add a pool-scoped lemma, e.g., `PoolFastImpliesNotarSubset(pool, s, h)`, that quantifies over `pool.certificates[s]` and asserts existence plus subset/equality for the stored pair. This removes ambiguity about cross-node timing.
- Consider a companion predicate for cross-type notar conflicts (if ever needed outside Pool), e.g., `CrossTypeNotarConflict(c1, c2) == c1.slot = c2.slot /\ c1.type ∈ NotarTypes /\ c2.type ∈ NotarTypes /\ c1.blockHash # c2.blockHash`, with a note referencing that Pool storage already enforces this.
- Add a brief reference in `Certificates.tla` near these predicates to the exact whitepaper lines (`:501`, `:520`, `:532`, `:534`, `:855`) to anchor readers.

```text
Audit scope: Certificates.tla predicates only. Broader invariants confirming the whitepaper (Lemma 24, Theorem 1) are enforced in MainProtocol.tla and VoteStorage.tla and were considered for context.
```

