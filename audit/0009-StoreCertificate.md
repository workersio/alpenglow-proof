# Audit: StoreCertificate(pool, cert)

## 1. Code Audited

```tla
StoreCertificate(pool, cert) ==
    IF CanStoreCertificate(pool, cert) /\ IsValidCertificate(cert) THEN
        [pool EXCEPT !.certificates[cert.slot] = 
            pool.certificates[cert.slot] \union {cert}]
    ELSE
        pool
```

## 2. Whitepaper Sections & References

- Tables 5–6 (vote and certificate kinds, thresholds): alpenglow-whitepaper.md:500
- Definition 12 (vote storage, count-once semantics): alpenglow-whitepaper.md:513
- Definition 13 (certificate generation/storage/broadcast): alpenglow-whitepaper.md:520
- Uniqueness statement (one certificate of each type per slot/block): alpenglow-whitepaper.md:532
- Implication note (fast ⇒ notar ⇒ fallback): alpenglow-whitepaper.md:534

Related protocol usage in the spec for context:
- Generate/store/broadcast certificates: specs/tla/alpenglow/MainProtocol.tla:200
- Deliver network certificates via Pool storage: specs/tla/alpenglow/MainProtocol.tla:520

## 3. Reasoning (Spec intent vs. whitepaper)

What the code does
- Guards: Stores a certificate iff both CanStoreCertificate(pool, cert) and IsValidCertificate(cert) hold.
- Effect: Adds the certificate to the slot-scoped set `pool.certificates[cert.slot]` via set union; idempotent under duplicates (set semantics).

How the guards align with the paper
- IsValidCertificate(cert) (in specs/tla/alpenglow/Certificates.tla:260) enforces Table 6 thresholds for the exact relevant vote subset by type/slot/block, plus basic typing (certificate type, slot, block hash domain, vote validity). This matches the “When enough votes are received, the respective certificate is generated” clause (Def. 13) and ensures only semantically valid certificates can be stored.
- CanStoreCertificate(pool, cert) (in specs/tla/alpenglow/VoteStorage.tla:109) captures the whitepaper’s uniqueness requirements:
  - For SkipCert and FinalizationCert (slot-scoped), at most one per type per slot.
  - For NotarizationCert, NotarFallbackCert, and FastFinalizationCert (block-scoped), it enforces both:
    - No duplicate by (type, blockHash) in the slot, and
    - Cross-type agreement on blockHash across the “notar family” within a slot. This strengthens the whitepaper’s implication note (fast ⇒ notar ⇒ fallback) into a storage-level block-consistency rule across those types.

Abstraction fit
- The function does not depend on local vote availability when accepting a network-learned certificate (only its validity and pool uniqueness), which is the right level of abstraction for Pool and agrees with Def. 13’s “received or constructed certificate is … stored and broadcast” intent.

External references involved
- CanStoreCertificate: specs/tla/alpenglow/VoteStorage.tla:109
- IsValidCertificate: specs/tla/alpenglow/Certificates.tla:260
- Certificate/typing helpers: specs/tla/alpenglow/Messages.tla:84

Where StoreCertificate is used
- Broadcast-on-generate path: specs/tla/alpenglow/MainProtocol.tla:232–244
- Deliver network certificate path: specs/tla/alpenglow/MainProtocol.tla:565–575

## 4. Conclusion

The StoreCertificate function correctly implements the whitepaper’s Definition 13 requirements at the Pool abstraction:
- Only valid (Table 6) certificates are accepted (IsValidCertificate).
- Uniqueness per slot and type is enforced, with an additional sound strengthening for notar-related cross-type block agreement (CanStoreCertificate).
- State update is idempotent and confined to the slot-scoped certificate set.

Given its usage sites (GenerateCertificateAction and DeliverCertificate), StoreCertificate aligns with the “generate, store, and broadcast” flow described in the whitepaper.

## 5. Open Questions / Concerns

- Skip vs Block certificate mutual exclusion at storage time:
  - The whitepaper’s prose and the model’s invariants intend that a slot does not simultaneously carry a SkipCert and any block-related certificate (Notarization/NotarFallback/FastFinalization). The system-level invariant PoolSkipVsBlockExclusion (specs/tla/alpenglow/MainProtocol.tla:867) enforces this globally.
  - However, CanStoreCertificate currently does not forbid storing a SkipCert when notar-related certificates already exist in the slot (and vice versa). The model relies on generation-side gating (VoteStorage.GenerateCertificate avoids producing skip if any block certificate is creatable) and global invariants to prevent such states. Cross-node skew could, in principle, still broadcast both types if created at different times by different nodes. The invariant should rule this out in reachable states; still, tightening local storage guards would make the exclusion explicit and self-contained.

- FinalizationCert acceptance independence:
  - StoreCertificate does not require that a corresponding notarization/finalization precondition is already present locally (e.g., “unique notarized block exists in slot s”). This matches the intention to accept valid network-learned certificates without relying on local votes; the actual use of FinalizationCert for finalizing a block is separately guarded in FinalizeBlock by the joint presence of FinalizationCert and NotarizationCert.

- Provenance checks for blockHash:
  - IsValidCertificate ensures `blockHash ∈ BlockHashes`, but does not prove the hash corresponds to an extant `b ∈ blocks`. The spec’s constructors only create certificates for real blocks; adversarial certificates are not injected (only adversarial votes are). This is consistent, but the assumption is implicit.

## 6. Suggestions for Improvement

- Enforce Skip vs Block mutual exclusion in storage:
  - Augment CanStoreCertificate with a guard that forbids storing a SkipCert if any notar-related certificate exists in the slot and forbids storing a notar-related certificate if a SkipCert exists. For example:
  ```tla
  HasBlockCert(existing) == \E c \in existing : c.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}
  CanStoreCertificate(pool, cert) ==
      LET existing == pool.certificates[cert.slot] IN
      CASE cert.type = "SkipCert" ->
               ~\E c \in existing : c.type = "SkipCert" /\ ~HasBlockCert(existing)
           [] cert.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"} ->
               ~\E c \in existing : c.type = cert.type /\ c.blockHash = cert.blockHash
            /\ (\A c \in existing : c.type \in {"NotarizationCert","NotarFallbackCert","FastFinalizationCert"} => c.blockHash = cert.blockHash)
            /\ ~\E c \in existing : c.type = "SkipCert"
           [] cert.type = "FinalizationCert" -> ~\E c \in existing : c.type = "FinalizationCert"
           [] OTHER -> FALSE
  ```
  - This makes the intended exclusion property local to Pool storage, reducing reliance on timing and inter-node skew.

- Strengthen invariants coverage:
  - Consider adding Certificates.FastPathImplication or VoteStorage.PoolFastImpliesNotarSubset as an invariant checked by MC to document “fast ⇒ notar with vote-subset” at the Pool level, complementing CertificateNonEquivocation. This aids auditability and aligns with the whitepaper’s implication note (alpenglow-whitepaper.md:534).

- Optional: provenance tightening (documentation):
  - Document (or optionally check) that any stored block-hash-bearing certificate references a block present in `blocks`. This is more a modeling clarity aid than a protocol requirement in the abstraction.

Overall, StoreCertificate is correct with respect to Definition 13. The suggested local Skip-vs-Block storage exclusion would further harden the spec against cross-node timing skew and make the intent explicit at the Pool boundary.

