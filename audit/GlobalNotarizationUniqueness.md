# Audit Report: GlobalNotarizationUniqueness

## 1. Code Under Audit

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

## 2. Whitepaper Section and References

The TLA+ code `GlobalNotarizationUniqueness` represents a critical safety property of the Alpenglow protocol, as described in the "Solana Alpenglow Consensus" whitepaper (v1.1, July 22, 2025). The most relevant sections are:

*   **Section 2.9: Safety**
    *   **Lemma 24:** "At most one block can be notarized in a given slot."
    *   **Lemma 21:** "fast-finalization property"
    *   **Lemma 26:** "slow-finalization property"
    *   **Theorem 1 (safety):** "If any correct node finalizes a block b in slot s and any correct node finalizes any block b' in any slot s' >= s, b' is a descendant of b."

## 3. Reasoning and Analysis

The TLA+ property `GlobalNotarizationUniqueness` asserts that for any given slot `s`, if any two correct nodes `v1` and `v2` hold notarization certificates (either `NotarizationCert` or `NotarFallbackCert`), then those certificates must be for the same block hash.

The whitepaper, in Section 2.9, provides a detailed proof for this property. The core argument is as follows:

1.  **Notarization Threshold:** To create a `NotarizationCert` or `NotarFallbackCert`, votes from nodes holding at least 60% of the total stake are required (Table 6).
2.  **Byzantine Stake:** The protocol assumes that byzantine nodes control less than 20% of the stake (Assumption 1).
3.  **Correct Node Stake:** This implies that for any notarization to occur, correct nodes holding at least 40% of the stake must have voted for it.
4.  **Exclusive Voting:** Lemma 20 states that a correct node will cast at most one notarization or skip vote per slot. This is enforced by the `Voted` state in the TLA+ model.

If two different blocks, `b1` and `b2`, were notarized in the same slot, it would require two distinct sets of votes, each accounting for at least 60% of the stake. This would necessitate an overlap of at least 20% of the stake voting for both blocks. Given the byzantine assumption, this overlap must contain at least some correct nodes. However, this would contradict the exclusive voting rule (Lemma 20), as a correct node cannot vote for two different blocks in the same slot.

The TLA+ code accurately captures this logic. It iterates through all slots and all pairs of correct nodes, and for each pair, it checks that any two notarization-related certificates they hold for the same slot must have the same block hash. This is a direct formalization of the uniqueness property described in the whitepaper.

## 4. Conclusion

The TLA+ code `GlobalNotarizationUniqueness` correctly and accurately represents the notarization uniqueness property as described in the Alpenglow whitepaper. The property is a direct formalization of Lemma 24 and is a cornerstone of the protocol's overall safety (Theorem 1). The audit finds no discrepancies between the TLA+ specification and the whitepaper's claims in this regard.

## 5. Open Questions or Concerns

*   The property `GlobalNotarizationUniqueness` is a global invariant. It is important to ensure that the model checker (TLC) is configured to check this invariant on all reachable states. The provided context does not include the TLC configuration file, but this is a crucial step for verification.
*   The property relies on the correctness of the `CorrectNodes` definition and the byzantine node model. Any errors in how byzantine behavior is modeled could potentially invalidate the verification of this property.

## 6. Suggestions for Improvement

*   The property could be made even more explicit by also checking that there are no conflicting `FastFinalizationCert`s, although this is implicitly covered by the logic (a `FastFinalizationCert` implies a `NotarizationCert`).
*   Consider adding a complementary property that checks for the liveness of notarization, i.e., that a block that should be notarized eventually is. This is a liveness property and would require a different kind of temporal logic expression (e.g., using `[]<>` - eventually always).