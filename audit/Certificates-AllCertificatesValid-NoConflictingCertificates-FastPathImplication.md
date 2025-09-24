# Audit: AllCertificatesValid, NoConflictingCertificates, FastPathImplication

## 1. Code that you are auditing

Source: `specs/tla/alpenglow/Certificates.tla:235`–`specs/tla/alpenglow/Certificates.tla:251`

```tla
\* All certificates must be valid
AllCertificatesValid(certificates) ==
    \A cert \in certificates : IsValidCertificate(cert)

\* No conflicting certificates should exist
NoConflictingCertificates(certificates) ==
    \A cert1, cert2 \in certificates :
        ~ConflictingCertificates(cert1, cert2)

\* Fast finalization implies notarization exists
FastPathImplication(certificates) ==
    \A fastCert \in certificates :
        fastCert.type = "FastFinalizationCert" =>
        \E notarCert \in certificates :
            /\ notarCert.type = "NotarizationCert"
            /\ notarCert.slot = fastCert.slot
            /\ notarCert.blockHash = fastCert.blockHash
```

Relevant operators referenced and defined nearby:
- `IsValidCertificate`: `specs/tla/alpenglow/Certificates.tla:190`–`specs/tla/alpenglow/Certificates.tla:206`
- `ConflictingCertificates`: `specs/tla/alpenglow/Certificates.tla:225`–`specs/tla/alpenglow/Certificates.tla:229`
- `FastFinalizationImpliesNotarization`: `specs/tla/alpenglow/Certificates.tla:217`–`specs/tla/alpenglow/Certificates.tla:222`
- Message/certificate types and structure: `specs/tla/alpenglow/Messages.tla:141`–`specs/tla/alpenglow/Messages.tla:155`

## 2. Whitepaper sections and references represented by the code

- Section 2.4 Votes and Certificates (message/certificate taxonomy)
  - Definition 11 (messages): `alpenglow-whitepaper.md:478`
  - Table 6 (certificate types, vote classes, thresholds): `alpenglow-whitepaper.md:490`–`alpenglow-whitepaper.md:510`
- Section 2.5 Pool (certificate generation/storage & uniqueness)
  - Definition 13 (certificates): `alpenglow-whitepaper.md:520`–`alpenglow-whitepaper.md:523`
  - Note: Fast-Finalization ⇒ Notarization ⇒ Notar-Fallback: `alpenglow-whitepaper.md:534`
- Finalization implications
  - Lemma 25 (“finalized implies notarized”): `alpenglow-whitepaper.md:860`–`alpenglow-whitepaper.md:866`
- Uniqueness across slots
  - Lemma 24 (at most one notarized block per slot): `alpenglow-whitepaper.md:852`–`alpenglow-whitepaper.md:864`

## 3. Reasoning: what the code asserts vs. the whitepaper

- AllCertificatesValid
  - Intent: Every certificate in a set satisfies the validity predicate.
  - In-model meaning: `IsValidCertificate` enforces per-type field well-formedness and stake thresholds:
    - FastFinalizationCert: 80% stake, `blockHash ∈ BlockHashes`.
    - Notarization/NotarFallback/Skip/Finalization: 60% stake; block field constraints (NoBlock for Skip/Finalization).
    - References: `specs/tla/alpenglow/Certificates.tla:190`–`:206`, Table 6 at `alpenglow-whitepaper.md:490`–`:510`.
  - Alignment: Thresholds match Table 6. The “count-once-per-slot” stake rule is implemented via `StakeFromVotes` with unique validators (Definition 12 underpinning).
  - Caveat: `IsValidCertificate` does not check that votes contained in the certificate match the certificate’s type and (slot, blockHash). E.g., it does not assert
    - ∀v ∈ cert.votes: v.slot = cert.slot,
    - ∀v ∈ cert.votes: v.type ∈ allowed types for cert.type (per Table 6),
    - For notar-type certs: ∀v ∈ cert.votes: v.blockHash = cert.blockHash.
    This is consistent with local constructors (which filter votes correctly), but weak for validating in-flight certificates (see `TransitCertificatesValid` in `specs/tla/alpenglow/MainProtocol.tla:877`–`:879`). The whitepaper’s Table 6 semantics imply these checks should hold.

- NoConflictingCertificates
  - Intent: No two certificates of the same type and slot disagree on block hash.
  - In-model meaning: `ConflictingCertificates` is defined as same slot ∧ same type ∧ different blockHash (`specs/tla/alpenglow/Certificates.tla:225`–`:229`). The quantified negation forbids such pairs inside the given set.
  - Alignment: This aligns with Definition 13’s “single certificate of each type for a given block/slot” as a uniqueness discipline within Pool (`alpenglow-whitepaper.md:520`–`:523`). It is weaker than Pool’s cross-type consistency rule (that notarization and notar-fallback agree on the same block), which is modeled elsewhere (e.g., `CanStoreCertificate` enforces cross-type coherence in Pool; `specs/tla/alpenglow/VoteStorage.tla:107`–`:124`, and system-level invariants `GlobalNotarizationUniqueness` in `specs/tla/alpenglow/MainProtocol.tla:818`–`:826`).

- FastPathImplication
  - Intent: If a fast-finalization certificate exists, a corresponding notarization certificate exists for the same (slot, blockHash).
  - In-model meaning: Existence of a matching `NotarizationCert` for each `FastFinalizationCert` in the set.
  - Alignment: Matches the whitepaper note that Table 6 implies Fast ⇒ Notar ⇒ Notar-Fallback (`alpenglow-whitepaper.md:534`). The module also provides a stronger binary relation `FastFinalizationImpliesNotarization` (requiring equal slot/hash and notar votes ⊆ fast votes) at `specs/tla/alpenglow/Certificates.tla:217`–`:222`. `FastPathImplication` captures the existence part of that statement over a set of certificates, consistent with the Pool behavior in Definition 13.

## 4. Conclusion of the audit

- The three predicates correctly capture high-level invariants implied by the whitepaper:
  - Validity per Table 6 thresholds, uniqueness of same-type certificates per slot, and fast-path implication of notarization presence.
- The abstractions are consistent with how Pool generates and stores certificates (Definition 13) and with system-level invariants in `MainProtocol.tla`.
- Primary concern: `IsValidCertificate` is too permissive for validating incoming certificates because it does not constrain the certificate’s vote set to match type, slot, and block, as required by Table 6 semantics. Consequently, `AllCertificatesValid` can hold for certificates assembled from mismatched or irrelevant votes if thresholds are met.
- Secondary observation: `NoConflictingCertificates` only guards same-type conflicts. Cross-type notarization consistency is modeled elsewhere, but documenting that relationship here would aid clarity.

Overall: Conceptual intent is aligned with the whitepaper, but strengthening vote-content checks in validity would improve soundness for transit validation and make the specification more self-contained.

## 5. Open questions or concerns

- Vote-type and binding checks in `IsValidCertificate`:
  - Should validity assert that certificate votes are drawn only from the allowed vote types per Table 6 and are bound to the certificate’s slot and block? This seems required by Definition 11/Table 6 semantics.
- Scope of the sets to which these predicates apply:
  - `FastPathImplication` is written for an arbitrary set of certificates. It holds by design for Pool’s `certificates[s]`, but may not hold for arbitrary subsets (e.g., a partial message set) where fast certs arrive before notarization certs. Is the intended domain “Pool certificates” only? If so, documenting this would clarify expectations.
- Cross-type conflict within a slot:
  - Should `NoConflictingCertificates` be broadened to cover notarization vs notar-fallback block disagreements for the same slot? Today that guarantee relies on Pool storage rules and separate system invariants.

## 6. Suggestions for improvement

- Strengthen `IsValidCertificate` to enforce vote-content constraints:
  - For notar-type certificates: `∀ v ∈ cert.votes: v.type = "NotarVote" (or NotarFallback for fallback), v.slot = cert.slot, v.blockHash = cert.blockHash`.
  - For fast-finalization: restrict to `NotarVote` only and the same `(slot, blockHash)`.
  - For skip/finalization: enforce `v.type ∈ {SkipVote, SkipFallbackVote}` or `v.type = FinalVote` and `v.blockHash = NoBlock`, with `v.slot = cert.slot`.
  - These checks align the validity predicate directly with Table 6 and Definition 11, closing the gap for `TransitCertificatesValid` (`specs/tla/alpenglow/MainProtocol.tla:877`–`:879`).

- Tighten `FastPathImplication` with the stronger relation already modeled:
  - Replace the existence clause with `\E notarCert ∈ certificates : FastFinalizationImpliesNotarization(fastCert, notarCert)` to also assert `notarCert.votes ⊆ fastCert.votes` (`specs/tla/alpenglow/Certificates.tla:217`–`:222`).

- Clarify conflict semantics in this module:
  - Either extend `ConflictingCertificates` to treat notarization and notar-fallback as a unified “notar-type” family for conflict purposes, or document that cross-type coherence is enforced by Pool rules (`specs/tla/alpenglow/VoteStorage.tla:107`–`:124`) and system invariants (`specs/tla/alpenglow/MainProtocol.tla:818`–`:826`).

- Document intended domain of the predicates:
  - Add a short note that these properties are intended to be checked on Pool’s `certificates[slot]` sets. This prevents misinterpretation when applied to arbitrary (possibly partial) certificate sets.

```refs
- Certificates.tla: specs/tla/alpenglow/Certificates.tla:190, :217, :225, :235, :239, :244
- Messages.tla: specs/tla/alpenglow/Messages.tla:141
- VoteStorage.tla: specs/tla/alpenglow/VoteStorage.tla:107, :178
- MainProtocol.tla: specs/tla/alpenglow/MainProtocol.tla:818, :849, :877
- Whitepaper: alpenglow-whitepaper.md:490, :520, :534, :852, :860
```

