# Audit Report: CertificateNonEquivocation

### 1. Code that you are auditing.
```tla
CertificateNonEquivocation ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET pool == validators[v].pool
        IN \A c1, c2 \in pool.certificates[slot] :
            (c1.type = c2.type /\ 
             c1.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}) =>
            c1.blockHash = c2.blockHash
```

### 2. The whitepaper section and references that the code represents.

This property is a direct formalization of the uniqueness rule from **Definition 13 (certificates)** on page 21 of the whitepaper:

> - A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool.

This property is also a necessary precondition for **Lemma 24** (at most one block can be notarized) and the related safety lemmas (21 and 26) to hold. If a node could hold multiple notarization certificates for different blocks in the same slot, the entire safety argument would collapse.

### 3. The reasoning behind the code and what the whitepaper claims.

The `CertificateNonEquivocation` property ensures that a validator's local `Pool` remains consistent and does not contain conflicting information. It prevents a situation where a node might certify two different blocks for the same purpose (e.g., notarization) in the same slot.

The TLA+ code formalizes this rule precisely:
1.  It iterates through each `CorrectNode` `v` and each `slot`.
2.  It then considers every pair of certificates, `c1` and `c2`, from that validator's pool for that specific slot.
3.  The `=>` (implication) is key. The left-hand side checks if the two certificates are of the *same type* and if that type is one of the notarization-family certificates (`NotarizationCert`, `NotarFallbackCert`, `FastFinalizationCert`).
4.  If the left-hand side is true, the right-hand side asserts that the certificates *must* be for the same block (`c1.blockHash = c2.blockHash`).

This logic correctly captures the "single certificate of each type" rule from Definition 13. The property is enforced operationally by the `CanStoreCertificate` predicate in `VoteStorage.tla`, which prevents a validator from storing a certificate that would violate this uniqueness constraint. This invariant then verifies that this enforcement is always successful and the property holds in every reachable state.

The property correctly excludes `SkipCert` and `FinalizationCert` from the block hash check, as these certificate types are not associated with a specific block hash (their `blockHash` field is `NoBlock`).

### 4. The conclusion of the audit.

The `CertificateNonEquivocation` TLA+ property is a **correct and accurate** formalization of the certificate uniqueness rule from Definition 13 of the Alpenglow whitepaper. It is a crucial safety property that prevents a validator from creating or accepting conflicting certificates, which is essential for the overall safety of the consensus protocol. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

None. The property is well-defined and correctly implements the intended constraint.