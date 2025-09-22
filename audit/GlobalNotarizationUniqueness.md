# Audit Report: GlobalNotarizationUniqueness

### 1. Code that you are auditing. 
```tla
GlobalNotarizationUniqueness ==
    \A s \in 1..MaxSlot :
        \A v1, v2 \in CorrectNodes :
            LET p1 == validators[v1].pool
                p2 == validators[v2].pool
            IN \A c1 \in p1.certificates[s], c2 \in p2.certificates[s] :
                   (c1.type \in {"NotarizationCert", "NotarFallbackCert"} /\
                    c2.type \in {"NotarizationCert", "NotarFallbackCert"}) =>
                   c1.blockHash = c2.blockHash
```

### 2. The whitepaper section and references that the code represents.

This property is a stronger, global version of **Lemma 24** (page 29). While Lemma 24 states that "at most one block can be notarized in a given slot," this TLA+ property ensures that this uniqueness holds *across all correct nodes*. If node A notarizes block `b1` and node B notarizes a block in the same slot, it must also be `b1`.

The reasoning is the same as for Lemma 24 but applied globally. For two different blocks to be notarized (or notarized-fallback), it would require two distinct sets of votes, each with >=60% stake. This would require an overlap of >40% of the stake if we consider the byzantine stake is <20%. This means correct nodes would have had to vote for two different blocks in the same slot, which violates **Lemma 20**.

### 3. The reasoning behind the code and what the whitepaper claims.

The `GlobalNotarizationUniqueness` property is a critical safety invariant that prevents forks at the notarization level across the entire network of correct nodes.

The TLA+ code formalizes this network-wide agreement:
1.  It iterates through every `slot` `s`.
2.  It considers every possible pair of `CorrectNodes`, `v1` and `v2`.
3.  It examines their respective pools, `p1` and `p2`.
4.  It then compares every notarization-related certificate (`NotarizationCert` or `NotarFallbackCert`) found in `p1` for slot `s` with every such certificate found in `p2` for the same slot `s`.
5.  The core assertion `=> c1.blockHash = c2.blockHash` requires that if both nodes have such a certificate for the same slot, the certificates must be for the exact same block hash.

This is a powerful and direct formalization of the idea that the "unique notarized block" is unique not just within one node's pool, but across the entire system of correct nodes. It correctly includes `NotarFallbackCert` in this check, as it also contributes to the notarized status of a block.

### 4. The conclusion of the audit.

The `GlobalNotarizationUniqueness` TLA+ property is a **correct and accurate** formalization of the global uniqueness guarantee implied by Lemma 24 and the underlying voting rules of the Alpenglow protocol. It correctly ensures that all correct nodes that observe a notarized block in a given slot will have observed the *same* block, preventing disagreements that could lead to forks. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

None. The property is well-specified and crucial for ensuring global safety.
