# Audit Report: NoConflictingFinalization

## 1. Code Under Audit

```tla
NoConflictingFinalization ==
    \A v1, v2 \in CorrectNodes :
    \A b1 \in finalized[v1], b2 \in finalized[v2] :
        (b1.slot = b2.slot) => b1.hash = b2.hash
```

## 2. Whitepaper Reference

*   **Section:** 2.9 Safety
*   **Reference:** This property is a direct corollary of **Theorem 1 (safety)**.

**Theorem 1:** "If any correct node finalizes a block $b$ in slot $s$ and any correct node finalizes any block $b'$ in any slot $s' \geq s$, $b'$ is a descendant of $b$."

The comment in the `MainProtocol.tla` file accurately describes this property as: "if two validators finalize blocks in the same slot, they must be identical."

## 3. Reasoning and Analysis

This property asserts that it is impossible for two different blocks to be finalized in the same slot across the network. This is a cornerstone of safety in any blockchain consensus protocol, as it prevents forks at the level of finalized blocks.

### Whitepaper Claim (Corollary of Theorem 1)

Theorem 1 guarantees that the set of all finalized blocks forms a single, linear chain of ancestry. A direct and critical consequence of this is that two distinct blocks cannot exist at the same height (slot). If two blocks, `b1` and `b2`, were finalized in the same slot (`b1.slot = b2.slot`) but had different hashes (`b1.hash != b2.hash`), then neither could be an ancestor of the other. This would violate the single-chain property guaranteed by Theorem 1.

Therefore, if any two finalized blocks share a slot number, they must also share the same hash, meaning they are the exact same block.

### TLA+ Code Implementation

The TLA+ code provides a direct and precise formalization of this corollary:

*   `\A v1, v2 \in CorrectNodes`: It considers any pair of correct nodes, `v1` and `v2`.
*   `\A b1 \in finalized[v1], b2 \in finalized[v2]`: It iterates through all blocks `b1` finalized by `v1` and all blocks `b2` finalized by `v2`.
*   `(b1.slot = b2.slot) => b1.hash = b2.hash`: This is the core assertion. It states that if block `b1` and block `b2` are for the same slot, then they must have the same hash. This elegantly captures the impossibility of finalizing conflicting blocks.

The implementation is a clear and correct translation of this fundamental safety property.

## 4. Conclusion

The `NoConflictingFinalization` TLA+ property is a **correct and accurate** formalization of a key safety guarantee that is a direct consequence of Theorem 1 in the Alpenglow whitepaper. It properly ensures that no two distinct blocks can be finalized in the same slot. The audit finds no correctness issues with this code.

## 5. Open Questions or Concerns

*   None. The property is fundamental, clearly stated, and correctly implemented.

## 6. Suggestions for Improvement

*   No improvements are suggested. The code is clear, concise, and its name accurately reflects its purpose.