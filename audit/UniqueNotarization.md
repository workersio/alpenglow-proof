# Audit Report: UniqueNotarization

### 1. Code that you are auditing.
```tla
UniqueNotarization ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET pool == validators[v].pool
            notarCerts == {c \in pool.certificates[slot] : 
                          c.type = "NotarizationCert"}
            notarBlocks == {c.blockHash : c \in notarCerts}
        IN Cardinality(notarBlocks) <= 1
```

### 2. The whitepaper section and references that the code represents.

This property directly corresponds to **Lemma 24** in Section 2.9 (page 29) of the whitepaper:

> **Lemma 24.** At most one block can be notarized in a given slot.

The proof of this lemma relies on Lemma 23 and ultimately on Lemma 20 (vote uniqueness), which I audited previously.

### 3. The reasoning behind the code and what the whitepaper claims.

The `UniqueNotarization` property is a crucial safety guarantee that prevents forks at the notarization stage. It ensures that for any given slot, the protocol cannot notarize two different blocks.

The whitepaper's reasoning is as follows:
1.  To notarize a block, votes from ≥60% of the stake are required (Definition 11/Table 6).
2.  Since byzantine nodes control <20% of the stake (Assumption 1), at least 40% of the stake for any notarization must come from correct nodes.
3.  If two different blocks were notarized in the same slot, it would require two sets of notarization votes, each from ≥60% of the stake. This would imply an overlap of at least 20% of the stake voting for both blocks.
4.  Given the byzantine stake, this overlap must contain correct nodes.
5.  However, this would violate Lemma 20, which states that a correct node can only cast one initial vote (notarization or skip) per slot.

The TLA+ code formalizes the *outcome* of this reasoning:
1.  It iterates through each `CorrectNode` `v` and each `slot`.
2.  `LET pool == validators[v].pool`: It examines the local pool of the validator.
3.  `notarCerts == {c \in pool.certificates[slot] : c.type = "NotarizationCert"}`: It filters the certificates in the pool for the given slot to find all `NotarizationCert`s.
4.  `notarBlocks == {c.blockHash : c \in notarCerts}`: It extracts the set of unique block hashes from these notarization certificates.
5.  `IN Cardinality(notarBlocks) <= 1`: This is the core assertion. It checks that the set of notarized block hashes for that slot contains at most one element.

This logic correctly verifies that no single correct node ever observes two different blocks being notarized in the same slot. While the property is checked on a per-node basis, the `GlobalNotarizationUniqueness` property (which I will likely audit later) extends this to ensure all correct nodes agree on the *same* single notarized block.

### 4. The conclusion of the audit.

The `UniqueNotarization` TLA+ property is a **correct and accurate** formalization of the safety guarantee described in Lemma 24 of the Alpenglow whitepaper. It correctly models the principle that at most one block can be notarized per slot from the perspective of a single correct node. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

None. The property is clear and directly maps to the corresponding lemma in the whitepaper.