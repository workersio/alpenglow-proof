# Audit Report for CertificateNonEquivocation

## 1. Code Under Audit

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

## 2. Whitepaper Section and References

*   **Whitepaper Section:** §2.5 Pool, specifically Definition 13.
*   **Definition 13 (certificates):** "A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool."
*   **Whitepaper Section:** §2.9 Safety, Lemma 24: Unique notarization.
*   **Lemma 24:** "At most one block can be notarized in a given slot."
*   **Whitepaper Section:** §2.9 Safety, Lemma 21 (fast-finalization property) and Lemma 26 (slow-finalization property). These lemmas imply that if a block is finalized, no other block can be notarized or notarized-fallback in the same slot.

## 3. Reasoning and Analysis

The TLA+ code `CertificateNonEquivocation` is a safety property that asserts that for any correct node `v` and any slot, if the node's `pool` contains two certificates of the same type (among "NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"), then they must be for the same block (i.e., have the same `blockHash`).

This directly corresponds to the principle of "non-equivocation" for certificates. A validator should not certify two different blocks for the same purpose in the same slot.

The whitepaper's Definition 13 in Section 2.5 states: "A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool." The TLA+ code is a formalization of this rule for the specified certificate types.

The property is also a direct consequence of the safety lemmas in Section 2.9. For example, Lemma 24 states that at most one block can be notarized in a given slot. This implies that a correct node cannot have two `NotarizationCert`s for different blocks in the same slot. The `CertificateNonEquivocation` property extends this to `NotarFallbackCert` and `FastFinalizationCert`.

## 4. Conclusion

The TLA+ code `CertificateNonEquivocation` correctly and accurately represents the non-equivocation property for certificates as described in the Alpenglow whitepaper. It is a crucial safety property that prevents a validator from creating or accepting conflicting certificates, which is essential for the overall safety of the consensus protocol. The code aligns with Definition 13 and is a necessary condition for the safety lemmas (21, 24, 26) to hold.

## 5. Open Questions or Concerns

*   The property is defined for `CorrectNodes`. This is appropriate for a safety property, as we are concerned with the behavior of non-faulty nodes. However, it's important to ensure that the overall system remains safe even when byzantine nodes equivocate. The safety proofs in the whitepaper (Section 2.9) seem to cover this, but it's worth keeping in mind.
*   The property only covers `NotarizationCert`, `NotarFallbackCert`, and `FastFinalizationCert`. It does not cover `SkipCert` or `FinalizationCert`. This is because `SkipCert` and `FinalizationCert` do not have a `blockHash` associated with them (it's `NoBlock`). This is consistent with the whitepaper.

## 6. Suggestions for Improvement

The code is clear and concise. No improvements are suggested.
