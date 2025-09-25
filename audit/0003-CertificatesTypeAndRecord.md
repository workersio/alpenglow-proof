# Audit: CertificateType and Certificate Record

1. Code Under Audit

```tla
CertificateType == {
    "FastFinalizationCert",  \* 80% threshold - one round finalization!
    "NotarizationCert",      \* 60% threshold - enables second round
    "NotarFallbackCert",     \* 60% threshold - mixed vote types OK
    "SkipCert",              \* 60% threshold - skip this slot
    "FinalizationCert"       \* 60% threshold - complete slow path
}

\* Structure of a certificate
Certificate == [
    type: CertificateType,                    \* Which certificate type
    slot: Slots,                              \* Which slot
    blockHash: BlockHashes \union {NoBlock},  \* Which block (or NoBlock)
    votes: SUBSET Vote                        \* The votes in this certificate
]
```

2. Whitepaper Sections and References

- Section 2.4 “Votes and Certificates”: `alpenglow-whitepaper.md:474`
- Definition 11 (messages): `alpenglow-whitepaper.md:478`
- Table 5 (vote messages): `alpenglow-whitepaper.md:491`
- Table 6 (certificate messages and thresholds): `alpenglow-whitepaper.md:501`
- Definition 13 (Pool generates, stores, broadcasts certificates): `alpenglow-whitepaper.md:520`
- Single certificate per type per block/slot; fast ⇒ notar ⇒ fallback: `alpenglow-whitepaper.md:532`
- Definition 14 (finalization semantics): `alpenglow-whitepaper.md:538`

3. Reasoning and Alignment With Whitepaper

- Certificate families (Table 6): The set `CertificateType` enumerates the five certificate types exactly as Table 6 specifies: Fast-Finalization, Notarization, Notar-Fallback, Skip, and Finalization. Names match the whitepaper terminology one-for-one (hyphenation differences only in identifiers).
- Threshold intent (Table 6): The comments annotate the intended thresholds (80% for fast; 60% for the rest). While the type block itself is declarative, these thresholds are enforced in `Certificates.tla` guard predicates and validators:
  - Guards: `CanCreateFastFinalizationCert`, `CanCreateNotarizationCert`, `CanCreateNotarFallbackCert`, `CanCreateSkipCert`, `CanCreateFinalizationCert` at `specs/tla/alpenglow/Certificates.tla:134`, `148`, `165`, `177`, `190`.
  - Validation: `IsValidCertificate` checks relevance, stake, and blockHash discipline at `specs/tla/alpenglow/Certificates.tla:268`.
- Certificate structure abstraction: The record schema `Certificate == [type, slot, blockHash, votes]` models a certificate as a set of votes meeting a threshold (an abstract stand-in for aggregate signatures over the same message, as per §1.6 and Table 6). This is consistent with the paper’s description that certificates aggregate per-validator signatures for the same message (block or slot).
- BlockHash discipline: Allowing `blockHash ∈ BlockHashes ∪ {NoBlock}` matches the two categories in Table 6:
  - Block-bearing certificates (Fast-Finalization, Notarization, Notar-Fallback) must carry a real `blockHash` and are checked as such in `IsValidCertificate` (`BlockHashes` branch): `specs/tla/alpenglow/Certificates.tla:286`, `289`.
  - Slot-scoped certificates (Skip, Finalization) intentionally carry `NoBlock` and are enforced in validation accordingly: `specs/tla/alpenglow/Certificates.tla:292`, `295`.
- Mixed vote types (Table 6): The permissive mix for Notar-Fallback (NotarVote or NotarFallbackVote) and Skip (SkipVote or SkipFallbackVote) is realized in the constructors and guards (e.g., `CreateNotarFallbackCert`, `CreateSkipCert`): `specs/tla/alpenglow/Certificates.tla:230`, `243`.
- Count-once-per-slot (Def. 12): Although the type permits any `SUBSET Vote`, stake aggregation deduplicates validators per slot before summing stake, aligning with Definition 12: `StakeFromVotes` and `UniqueValidators` at `specs/tla/alpenglow/Certificates.tla:88`, `84`.
- Pool integration (Defs. 13–16): The Pool stores certificates typed as `Certificate`, enforcing uniqueness and generation rules consistent with the whitepaper:
  - Pool structure typing includes `certificates: [Slots -> SUBSET Certificate]`: `specs/tla/alpenglow/VoteStorage.tla:20`.
  - Store rules enforce uniqueness per type and block/slot; and ensure only valid certificates are stored: `CanStoreCertificate` and `StoreCertificate` at `specs/tla/alpenglow/VoteStorage.tla:61`, `83`.
  - Generation follows the guard hierarchy, matching “fast ⇒ notar ⇒ fallback” and skip gating: `GenerateCertificate` at `specs/tla/alpenglow/VoteStorage.tla:110`.

4. Conclusion of the Audit

- The audited code correctly specifies the certificate type universe and the abstract shape of a certificate in a way that aligns with the whitepaper’s Table 6 and Definitions 13–14.
- Downstream modules (`Certificates.tla`, `VoteStorage.tla`) enforce the threshold logic, relevance of votes, blockHash discipline, and Pool storage/uniqueness rules, collectively matching Sections 2.4–2.5.
- There is no conceptual mismatch between the whitepaper’s abstraction (aggregated signatures for the same message) and the TLA model (sets of votes), provided we maintain the “relevant votes only” property, which is available as `CertificateWellFormed` (see suggestions).

5. Open Questions or Concerns

- Structural strictness of `Certificate.votes`:
  - `IsValidCertificate` computes stake from the relevant subset of `cert.votes` but does not require `cert.votes ⊆ RelevantVotes` (this check is in `CertificateWellFormed`, separate from acceptance). This means certificates could contain extraneous, irrelevant votes without affecting acceptance. The whitepaper’s aggregate-signature framing implies signatures over the same message only; extraneous votes would be un-signable in practice.
- Enforcement locus:
  - `VoteStorage.StoreCertificate` uses `IsValidCertificate` but does not require `CertificateWellFormed(cert)`. If we want the model to mirror “same-message aggregation” more literally, we should require the structural check on store.

6. Suggestions for Improvement

- Enforce well-formedness on store:
  - Strengthen `StoreCertificate` to require `CertificateWellFormed(cert)` in addition to `IsValidCertificate(cert)`: `specs/tla/alpenglow/VoteStorage.tla:83`.
  - Alternatively, assert a global invariant where certificates are stored (e.g., `AllCertificatesWellFormed(pool.certificates[s])` for each slot) to capture the same-message constraint.
- Optional: Add an explicit invariant that Pool’s certificate sets satisfy cross-implication properties scoped to a single Pool (fast ⇒ notar with vote-subset inclusion), similar to `PoolFastImpliesNotarSubset`: `specs/tla/alpenglow/VoteStorage.tla:174`.
- Documentation note: Keep the comment near `Certificate` clarifying that NoBlock is intentional for slot-scoped certificates (Skip/Finalization) and that relevance filtering happens during validation; this is already clearly documented but can be cross-linked to `IsValidCertificate` for quick navigation.

7. References Found in Code (for this block’s context)

- Where this code lives in repo:
  - `specs/tla/alpenglow/Messages.tla:142` (CertificateType)
  - `specs/tla/alpenglow/Messages.tla:151` (Certificate)
- Types used by this block:
  - `specs/tla/alpenglow/Messages.tla:44` (VoteType), `specs/tla/alpenglow/Messages.tla:53` (Vote)
  - `specs/tla/alpenglow/Messages.tla:163` (IsValidVote)
- Downstream certificate logic:
  - Guards: `specs/tla/alpenglow/Certificates.tla:134`, `148`, `165`, `177`, `190`
  - Constructors: `specs/tla/alpenglow/Certificates.tla:216`, `223`, `230`, `243`, `252`
  - Validation: `specs/tla/alpenglow/Certificates.tla:268`
  - Well-formedness: `specs/tla/alpenglow/Certificates.tla:303`
- Pool integration:
  - Types and storage: `specs/tla/alpenglow/VoteStorage.tla:20`, `61`, `83`
  - Generation: `specs/tla/alpenglow/VoteStorage.tla:110`

