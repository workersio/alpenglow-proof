# Audit: `CreateFastFinalizationCert`

## 1. Code Audited

```tla
CreateFastFinalizationCert(votes, slot, blockHash) ==
    [type |-> "FastFinalizationCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type = "NotarVote" /\ v.slot = slot /\ v.blockHash = blockHash}]
```

Context in repo:
- Definition location: `specs/tla/alpenglow/Certificates.tla:149`
- Related constructor calls: `specs/tla/alpenglow/VoteStorage.tla:181`, `specs/tla/alpenglow/VoteStorage.tla:185`, `specs/tla/alpenglow/VoteStorage.tla:187`
- Certificate type definition: `specs/tla/alpenglow/Messages.tla:142`

## 2. Whitepaper Sections and References

- Table 6 (Certificate messages and thresholds):
  - Fast-Finalization Cert.: NotarVote; Σ ≥ 80% — `alpenglow-whitepaper.md:501`
  - Notarization Cert.: NotarVote; Σ ≥ 60% — `alpenglow-whitepaper.md:502`
  - Notar-Fallback Cert.: NotarVote or NotarFallbackVote; Σ ≥ 60% — `alpenglow-whitepaper.md:503`
  - Finalization Cert.: FinalVote; Σ ≥ 60% — `alpenglow-whitepaper.md:505`
  - Table caption (Σ definition): `alpenglow-whitepaper.md:507`
- Definition 12 (storing votes; count-once-per-slot): `alpenglow-whitepaper.md:513`
- Definition 13 (certificates; generate when enough votes; store one per type): `alpenglow-whitepaper.md:520`
- Implication: Fast-Finalization ⇒ Notarization ⇒ Notar-Fallback: `alpenglow-whitepaper.md:534`

## 3. Reasoning and Alignment With Whitepaper

- Enforced aggregated vote type
  - The constructor filters to `v.type = "NotarVote"` for the given `slot` and `blockHash`.
  - This matches Table 6’s Fast-Finalization requirement that only NotarVote messages are aggregated for fast finalization (`alpenglow-whitepaper.md:501`). It correctly excludes NotarFallbackVote and any other vote types.

- Separation of construction vs. threshold checking
  - This function only constructs the certificate record; it does not itself check the 80% threshold — consistent with TLA+ separation of concerns.
  - Threshold checks happen either before construction (`CanCreateFastFinalizationCert` uses 80%: `specs/tla/alpenglow/Certificates.tla:83`–`88`) or via validation (`IsValidCertificate` uses 80% for fast certs: `specs/tla/alpenglow/Certificates.tla:190`, `specs/tla/alpenglow/Certificates.tla:196`).

- Count-once-per-slot stake aggregation
  - Whitepaper Definition 12 requires counting each validator’s stake at most once per slot (`alpenglow-whitepaper.md:513`).
  - The spec implements this in stake helpers: `UniqueValidators` and `StakeFromVotes` (`specs/tla/alpenglow/Certificates.tla:60`, `specs/tla/alpenglow/Certificates.tla:64`). Thus, even if the input `votes` set contained multiple messages per validator, stake is aggregated once.
  - In practice, `VoteStorage` enforces per-validator multiplicity (store first Notar/Skip vote; up to 3 fallback, etc.), preventing duplicated initial votes in Pool (`specs/tla/alpenglow/VoteStorage.tla:41`–`53`, `specs/tla/alpenglow/VoteStorage.tla:102`).

- Integration in Pool (Definition 13)
  - Certificates are generated when enough votes exist (`alpenglow-whitepaper.md:520`), implemented by `GenerateCertificate`, which calls `CreateFastFinalizationCert` only if `CanCreateFastFinalizationCert` holds (`specs/tla/alpenglow/VoteStorage.tla:181`, `specs/tla/alpenglow/VoteStorage.tla:185`, `specs/tla/alpenglow/VoteStorage.tla:187`).
  - When fast-finalization is possible, the implementation also creates the Notarization and Notar-Fallback certificates for the same block, reflecting the Table 6 implication (`alpenglow-whitepaper.md:534`).

- Typing and consistency
  - The constructed record uses a valid certificate type (`Messages.tla:142`), carries the `slot` and `blockHash`, and gathers the relevant `votes`. General certificate typing and value checks are captured in `IsValidCertificate` (`specs/tla/alpenglow/Certificates.tla:190`).

## 4. Conclusion of the Audit

- The constructor `CreateFastFinalizationCert` correctly captures the Table 6 abstraction for the fast-finalization certificate by aggregating exactly the notarization votes (`NotarVote`) for a specific block and slot.
- Threshold enforcement (Σ ≥ 80%) and the count-once-per-slot rule are handled by adjacent predicates (`CanCreateFastFinalizationCert`, `IsValidCertificate`) and stake helpers, aligning with Definitions 12 and 13.
- Integrated with `VoteStorage.GenerateCertificate`, the behavior matches the whitepaper’s implication that fast finalization entails the existence of the 60% certificates for the same block.

Overall, the code accurately represents the whitepaper’s abstraction for fast-finalization certificate construction.

## 5. Open Questions / Concerns

- Certificate vote-type validation
  - `IsValidCertificate` enforces thresholds but does not assert that the `cert.votes` set contains only vote types permitted by the certificate category (e.g., only `NotarVote` for fast-finalization). If a malformed or adversarial certificate were injected from the network, it might still pass `IsValidCertificate` if the stake threshold is met.
  - This is mitigated if the system assumes certificates are only created via the trusted constructors in this module and validated upstream, but the spec currently allows external `cert` objects to be stored after only uniqueness checks (`specs/tla/alpenglow/VoteStorage.tla:139`–`163`).

- Duplicates in `cert.votes`
  - While stake counting uses unique validators and Pool limits initial votes, the constructor does not deduplicate messages in `cert.votes`. This is fine semantically, but the spec could optionally document that `cert.votes` might contain multiple messages from the same validator (e.g., if formed from unfiltered sets) though stake is counted once.

## 6. Suggestions for Improvement

- Strengthen certificate validation to check allowed vote types per certificate:
  - For fast/notarization: all `v ∈ cert.votes` satisfy `v.type = "NotarVote"`.
  - For notar-fallback: all `v.type ∈ {"NotarVote", "NotarFallbackVote"}`.
  - For skip: all `v.type ∈ {"SkipVote", "SkipFallbackVote"}` and `cert.blockHash = NoBlock`.
  - For finalization: all `v.type = "FinalVote"` and `cert.blockHash = NoBlock`.
  - Implement as guards in `IsValidCertificate` to enforce Table 6 structurally, not only by threshold.

- Optional: add a lemma or comment near `CreateFastFinalizationCert` documenting that the constructor intentionally filters to `NotarVote` only (fast path excludes fallback votes), with a reference to Table 6 (`alpenglow-whitepaper.md:501`).

- Optional: explicitly deduplicate `cert.votes` by `validator` when constructing certificates, to make the representation canonical (stake is already unique, but canonical sets ease reasoning and comparison), or document that canonicalization is not required for correctness.

