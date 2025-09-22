# Audit Report: FinalizedImpliesNotarized

### 1. Code that you are auditing.
```tla
FinalizedImpliesNotarized ==
    \A v \in CorrectNodes :
    \A b \in finalized[v] :
        LET pool == validators[v].pool
        IN \E cert \in pool.certificates[b.slot] :
            /\ cert.type \in {"NotarizationCert", "FastFinalizationCert"}
            /\ cert.blockHash = b.hash
```

### 2. The whitepaper section and references that the code represents.

This property directly corresponds to **Lemma 25** in Section 2.9 (page 30) of the whitepaper:

> **Lemma 25.** *If a block is finalized by a correct node, the block is also notarized.*

The proof in the whitepaper considers the two paths to finalization from **Definition 14 (finalization)** (page 21):
*   **Fast Finalization:** Requires a `FastFinalizationCert`, which implies a `NotarizationCert` because the stake threshold is higher (80% > 60%).
*   **Slow Finalization:** Requires a `FinalizationCert` for the slot *and* the block to be the "unique notarized block in slot s". This explicitly requires the block to be notarized.

### 3. The reasoning behind the code and what the whitepaper claims.

The `FinalizedImpliesNotarized` property is a fundamental safety check ensuring that the finalization process respects the underlying notarization mechanism. A block cannot be considered final without first having achieved a high level of support, which is what notarization represents.

The TLA+ code formalizes this by checking the preconditions for finalization:
1.  It iterates through each `CorrectNode` `v` and every block `b` that `v` has finalized.
2.  It then asserts that in the validator's `pool` for that block's `slot`, there must exist a certificate `cert` that satisfies two conditions:
    *   `cert.type \in {"NotarizationCert", "FastFinalizationCert"}`: The certificate must be either a `NotarizationCert` or a `FastFinalizationCert`.
    *   `cert.blockHash = b.hash`: The certificate must be for the specific block `b` that was finalized.

This logic correctly covers both finalization paths described in the whitepaper and the `FinalizeBlock` action in `MainProtocol.tla`:
*   If the block was **fast-finalized**, a `FastFinalizationCert` for that block must exist in the pool. The property is satisfied.
*   If the block was **slow-finalized**, a `NotarizationCert` for that block must exist in the pool (along with a `FinalizationCert` for the slot). The property is satisfied.

The TLA+ code is a direct and accurate translation of the logic presented in Lemma 25.

### 4. The conclusion of the audit.

The `FinalizedImpliesNotarized` TLA+ property is a **correct and accurate** formalization of the safety guarantee described in Lemma 25 of the Alpenglow whitepaper. It correctly verifies that any finalized block must have a corresponding notarization or fast-finalization certificate, which is a cornerstone of the protocol's two-step finalization logic. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

None. The property is clear, concise, and correctly specified.