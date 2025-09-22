
# Audit Report for UniqueNotarization

## 1. Code Under Audit

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

## 2. Whitepaper Section and References

This TLA+ code corresponds to **Lemma 24** in the Alpenglow whitepaper (page 29).

**Lemma 24:** At most one block can be notarized in a given slot.

The proof of this lemma in the whitepaper relies on:
*   **Definition 11:** which specifies that a "Notarization Cert." requires >= 60% of the stake.
*   **Assumption 1:** Byzantine nodes control less than 20% of the stake.
*   **Lemma 23:** If correct nodes with more than 40% of stake cast notarization votes for block `b`, no other block can be notarized in the same slot.
*   **Lemma 20:** A correct node exclusively casts only one notarization vote or skip vote per slot.

## 3. Reasoning and Analysis

The TLA+ property `UniqueNotarization` formalizes Lemma 24 by asserting a critical safety invariant. Let's break down the TLA+ code and connect it to the whitepaper's claims.

*   `\A v \in CorrectNodes`: This iterates over all correct (non-Byzantine) nodes. The property must hold for every honest participant in the network.
*   `\A slot \in 1..MaxSlot`: This iterates over all possible slots in the model. The property must hold for every slot.
*   `LET pool == validators[v].pool`: Each validator maintains a local `pool` of votes and certificates, as described in Section 2.5 of the whitepaper.
*   `notarCerts == {c \in pool.certificates[slot] : c.type = "NotarizationCert"}`: This line filters the certificates in the pool for a specific `slot` to find all certificates of type `NotarizationCert`. This directly corresponds to the "Notarization Cert." mentioned in Table 6 of the whitepaper.
*   `notarBlocks == {c.blockHash : c \in notarCerts}`: This extracts the set of unique block hashes from the notarization certificates found in the previous step.
*   `IN Cardinality(notarBlocks) <= 1`: This is the core assertion. It states that the number of unique block hashes that have been notarized in a given slot, from the perspective of a correct node, must be less than or equal to one.

The TLA+ code correctly models the claim in Lemma 24. If this property holds, it means that no correct node will ever observe two different blocks being notarized in the same slot. This is a cornerstone of the protocol's safety, preventing forks at the notarization stage.

The reasoning in the whitepaper is that for a block to be notarized, it needs 60% of the stake. Since less than 20% of the stake is Byzantine, at least 40% of the stake must come from correct nodes. If two different blocks were notarized in the same slot, it would imply that some correct nodes voted for both, which is forbidden by Lemma 20 (vote uniqueness). The TLA+ property checks the *outcome* of this logic: that at the end of the day, a correct node's pool never contains notarization certificates for two different blocks in the same slot.

## 4. Conclusion of the Audit

The TLA+ property `UniqueNotarization` is a correct and accurate formalization of Lemma 24 from the Alpenglow whitepaper. It is a critical safety property that helps ensure the overall safety of the protocol. The implementation of this check in the TLA+ model is sound and directly reflects the intended behavior described in the whitepaper.

## 5. Open Questions or Concerns

None. The property is clear and its implementation is straightforward.

## 6. Suggestions for Improvement

The property `UniqueNotarization` is scoped to a single validator's pool (`\A v \in CorrectNodes`). While this is a valid and important check, the whitepaper also implies a stronger, global property. The `MainProtocol.tla` file already includes a `GlobalNotarizationUniqueness` property which asserts this stronger guarantee across all correct nodes. It would be beneficial to explicitly link the audit of `UniqueNotarization` to `GlobalNotarizationUniqueness` and explain how they work together to prove the overall safety claim.

Specifically, `UniqueNotarization` ensures that a single node doesn't get confused, while `GlobalNotarizationUniqueness` ensures that different nodes don't have conflicting views of what's notarized. Both are necessary.
