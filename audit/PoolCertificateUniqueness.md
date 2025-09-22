# Audit Report: PoolCertificateUniqueness

### 1. Code that you are auditing.
```tla
PoolCertificateUniqueness ==
    \A v \in Validators : CertificateUniqueness(validators[v].pool)
```

### 2. The whitepaper section and references that the code represents.

This property directly corresponds to **Definition 13 (certificates)** in Section 2.5 (page 21) of the whitepaper:

> - A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool.

### 3. The reasoning behind the code and what the whitepaper claims.

The `PoolCertificateUniqueness` property ensures that the certificate storage rules from the whitepaper are respected within each validator's pool. This is a crucial invariant for consistency, preventing a node from holding conflicting certificates (e.g., two different notarization certificates for the same slot).

The TLA+ code is structured in two layers:
1.  `PoolCertificateUniqueness`: The top-level invariant, which simply iterates through all validators and applies the `CertificateUniqueness` check to each of their pools.
2.  `CertificateUniqueness(pool)`: This helper predicate, defined in `VoteStorage.tla`, implements the core logic.

The definition of `CertificateUniqueness` is:
```tla
CertificateUniqueness(pool) ==
    \A s \in Slots :
        \A c1, c2 \in pool.certificates[s] :
            (c1.type = c2.type /\ c1.slot = c2.slot) =>
            (c1.type \in {"SkipCert", "FinalizationCert"} \/ c1.blockHash = c2.blockHash)
```
This logic can be broken down as follows:
*   For any given slot `s` in a `pool`.
*   For any two certificates `c1` and `c2` in that slot's certificate list.
*   If the certificates are of the same `type` and for the same `slot`...
*   ...then one of two conditions must be true:
    1.  The certificate type is one that is not block-specific (`SkipCert` or `FinalizationCert`). In this case, having two of the same type implicitly means they are duplicates of the same certificate, which is allowed.
    2.  The certificates must be for the same block (`c1.blockHash = c2.blockHash`). This applies to `NotarizationCert`, `NotarFallbackCert`, and `FastFinalizationCert`.

This is a precise and correct formalization of the rule from Definition 13. It ensures that for any given slot, a pool cannot contain two notarization-family certificates for different blocks. The operational enforcement is handled by the `CanStoreCertificate` predicate, and this invariant serves as a global check that the rule is never violated.

This property is very similar to `CertificateNonEquivocation`. The key difference is that `CertificateUniqueness` is a property *within* a single pool's data structure, while `CertificateNonEquivocation` is a property that holds *for a correct node's pool*. They are checking very similar conditions, but at slightly different levels of abstraction and scope. `PoolCertificateUniqueness` applies to *all* validators, including byzantine ones, ensuring the data structure rules are universally respected.

### 4. The conclusion of the audit.

The `PoolCertificateUniqueness` TLA+ property, via its helper `CertificateUniqueness`, is a **correct and accurate** formalization of the certificate storage uniqueness rule from Definition 13 of the Alpenglow whitepaper. It correctly ensures that no validator's pool can contain conflicting certificates for the same slot. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

None. The property is well-defined and correctly models the whitepaper's specification.
