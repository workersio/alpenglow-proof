# Audit: VoteStorage.CanStoreCertificate

## 1. Code Being Audited

Source: `specs/tla/alpenglow/VoteStorage.tla:109`

```
CanStoreCertificate(pool, cert) ==
    LET 
        slot == cert.slot
        existing == pool.certificates[slot]
        NotarTypes == {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}
    IN
        CASE cert.type \in {"SkipCert", "FinalizationCert"} ->
            \* At most one SkipCert and one FinalizationCert per slot
            ~\E c \in existing : c.type = cert.type

        [] cert.type \in NotarTypes ->
            /\ ~\E c \in existing : c.type = cert.type /\ c.blockHash = cert.blockHash
            /\ \A c \in existing :
                  c.type \in NotarTypes => c.blockHash = cert.blockHash

        [] OTHER -> FALSE
```

Related surrounding context:
- `specs/tla/alpenglow/VoteStorage.tla:131` — `StoreCertificate` uses `CanStoreCertificate` and `IsValidCertificate` to accept certificates.
- `specs/tla/alpenglow/VoteStorage.tla:176` — `GenerateCertificate` creates block- and slot-level certs and gates SkipCerts when any block cert is creatable.
- Invariants and cross-module checks:
  - `specs/tla/alpenglow/MainProtocol.tla:853` — `CertificateNonEquivocation` (per-slot, per-type uniqueness on block hash).
  - `specs/tla/alpenglow/MainProtocol.tla:806` — `UniqueNotarization` (at most one notarized block hash per slot per pool).
  - `specs/tla/alpenglow/MainProtocol.tla:839` — `FinalizedImpliesNotarized`.
  - `specs/tla/alpenglow/MainProtocol.tla:870` — `PoolSkipVsBlockExclusion` (delegates to Certificates).
  - `specs/tla/alpenglow/Certificates.tla:436` — `SkipVsBlockCertExclusion` (no SkipCert coexisting with block-related certs in a slot).

## 2. Whitepaper Sections and References

- Pool and certificate storage rules:
  - `alpenglow-whitepaper.md:510` — Definition 12 (storing votes; multiplicity constraints).
  - `alpenglow-whitepaper.md:520` — Definition 13 (certificates: generate, store, broadcast).
  - `alpenglow-whitepaper.md:532` — “A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool.”
- Certificate types and thresholds (context):
  - Table 6 (votes/certificates, thresholds) — §2.4 around `alpenglow-whitepaper.md:474`–`:520`.
- Finalization semantics (context):
  - `alpenglow-whitepaper.md:536` — Definition 14 (fast vs slow finalization semantics).

## 3. Reasoning (Mapping Code ↔ Whitepaper)

- Goal of the predicate
  - Enforce the Pool’s per-slot certificate uniqueness constraints per Definition 13: for each slot, store at most one certificate of each type, and ensure notarization-family certificates are consistent on a single block hash.

- Case analysis
  - SkipCert and FinalizationCert (per-slot certificates):
    - Code: Prohibits storing a second certificate of the same type in the slot.
    - Paper: Fits “single certificate of each type … for the given block/slot”. These types are slot-scoped (no `blockHash`).
  - NotarizationCert, NotarFallbackCert, FastFinalizationCert (per-block-in-slot certificates):
    - First conjunct `~∃ c ∈ existing: c.type = cert.type ∧ c.blockHash = cert.blockHash` prevents duplicates of the same type for the same block.
    - Second conjunct `∀ c ∈ existing: c.type ∈ NotarTypes ⇒ c.blockHash = cert.blockHash` enforces that all notar-family certificates in a slot agree on the same block hash. This realizes “single notarized block per slot” and permits storing one of each type for that block, matching the whitepaper’s note that fast-finalization implies notarization implies notar-fallback.

- Interactions and supporting invariants
  - `GenerateCertificate` only emits `SkipCert` when no block certificate is creatable, aligning operationally with the mutually exclusive conditions of §2.6.
  - Cross-check invariants in `MainProtocol` and `Certificates` (UniqueNotarization, CertificateNonEquivocation, Skip-vs-Block exclusion) collectively guarantee that no pool and no pair of correct pools can hold conflicting notar-family certificates in the same slot.

## 4. Conclusion of the Audit

- The predicate correctly enforces Definition 13’s storage discipline:
  - At most one `SkipCert` and one `FinalizationCert` per slot.
  - At most one of each notar-family type per block within a slot, while ensuring all notar-family certificates in a slot share the same block hash.
- This matches the whitepaper’s “single certificate of each type … for the given block/slot” and the intended implication chain among notar-family certificates.
- The design intentionally keeps acceptance separate from local vote availability by delegating threshold checks to `IsValidCertificate` and leaving mutually exclusive conditions (skip vs block) to higher-level generation logic and invariants. This is reasonable at the abstraction level and consistent with the paper.

## 5. Open Questions or Concerns

- Skip vs Block coexistence on acceptance path:
  - `CanStoreCertificate` does not reject a `SkipCert` when block-related certificates are already stored (and vice versa). Practically, `GenerateCertificate` avoids creating both, and with <20% Byzantine stake the thresholds prevent both from being valid simultaneously. Still, acceptance could be tightened to reduce state space and guard against malformed inputs.
- Cross-pool timing: The model accepts network-learned certificates based on their internal votes (`IsValidCertificate`). This is faithful to the whitepaper’s broadcast rule but means local Pool vote contents are not used to validate incoming certificates; invariants must catch any cross-certificate inconsistencies.
- Redundancy vs clarity: The per-type duplicate check and the cross-type hash-consistency check both contribute. They are necessary together to forbid duplicate same-type certs for the same block and forbid conflicting blocks across notar types; this is correct but worth documenting as intentional.

## 6. Suggestions for Improvement

- Optional store-time exclusion for skip vs block:
  - Add a guard to `CanStoreCertificate` to enforce `SkipVsBlockCertExclusion(existing ∪ {cert})`. This encodes the mutually exclusive nature directly at the acceptance point and trims unreachable states under the model’s assumptions.
- Document acceptance rationale in `StoreCertificate`:
  - Clarify in comments that acceptance is independent of local vote availability to avoid dropping valid network-learned certificates (already partially noted). Emphasize that invariants (`PoolSkipVsBlockExclusion`, `CertificateNonEquivocation`) are relied upon for safety.
- Strengthen invariants usage:
  - Ensure `PoolCertificateUniqueness` and `PoolSkipVsBlockExclusion` remain part of the top-level conjunct of `Spec`/`Inv` (they are present in `MainProtocol`, keep them enabled during MC runs).
- Traceability notes:
  - Consider adding an explicit lemma-like property in `VoteStorage` tying the stored notar-family certificates to a unique `blockHash` per slot (the code enforces it; a named property aids model checking and readability, similar to `UniqueNotarization`).

```tla
\* Example guard (optional):
CanStoreCertificate(pool, cert) ==
  LET ex == pool.certificates[cert.slot] IN
    SkipVsBlockCertExclusion(ex \cup {cert}) /\ ... existing checks ...
```

