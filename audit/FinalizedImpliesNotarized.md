# Audit Report: FinalizedImpliesNotarized

## 1. Code Under Audit

```tla
FinalizedImpliesNotarized ==
    \A v \in CorrectNodes :
    \A b \in finalized[v] :
        LET pool == validators[v].pool
        IN \E cert \in pool.certificates[b.slot] :
            /\ cert.type \in {"NotarizationCert", "FastFinalizationCert"}
            /\ cert.blockHash = b.hash
```

## 2. Whitepaper Reference

This TLA+ code corresponds to **Lemma 25** on page 30 of the Alpenglow whitepaper (`alpenglow-whitepaper.md`).

**Lemma 25:** *If a block is finalized by a correct node, the block is also notarized.*

## 3. Reasoning and Analysis

The TLA+ code specifies that for any correct node `v` and any block `b` that `v` has finalized, there must exist a certificate in `v`'s pool for that block's slot. This certificate must be of type `NotarizationCert` or `FastFinalizationCert` and must correspond to the block's hash.

The whitepaper's proof for Lemma 25 considers two cases for finalization:

1.  **Fast Finalization:** A block is fast-finalized if it receives a `FastFinalizationCert`, which requires notarization votes from >=80% of the stake. The TLA+ code correctly captures this by checking for the existence of a `FastFinalizationCert`. The whitepaper notes that a `FastFinalizationCert` implies a `NotarizationCert` exists because the stake threshold is higher (80% > 60%). The TLA+ code allows for either, which is correct.

2.  **Slow Finalization:** A block is slow-finalized if it receives a `FinalizationCert` (>=60% stake) for its slot, and the block itself has been notarized. The `FinalizeBlock` action in `MainProtocol.tla` shows that slow finalization requires a `NotarizationCert` and a `FinalizationCert`.

The TLA+ property `FinalizedImpliesNotarized` checks for a `NotarizationCert` or a `FastFinalizationCert`. This seems to correctly capture the conditions for both fast and slow finalization. If a block is fast-finalized, a `FastFinalizationCert` will be present. If a block is slow-finalized, a `NotarizationCert` must be present.

The TLA+ code is a direct and accurate translation of the property described in Lemma 25.

## 4. Conclusion

The TLA+ code `FinalizedImpliesNotarized` correctly and accurately represents the property stated in Lemma 25 of the Alpenglow whitepaper. The logic in the TLA+ code aligns with the reasoning provided in the whitepaper's proof for both fast and slow finalization paths.

## 5. Open Questions or Concerns

None. The code and the whitepaper are in clear alignment on this property.

## 6. Suggestions for Improvement

None. The TLA+ specification for this lemma is clear and concise.
