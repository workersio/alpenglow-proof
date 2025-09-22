# Audit Report: MainProtocol-SafetyInvariant

## 1. Code Under Audit

```tla
SafetyInvariant ==
    \A v1, v2 \in CorrectNodes :
    \A b1 \in finalized[v1], b2 \in finalized[v2] :
        (b1.slot <= b2.slot) => IsAncestor(b1, b2, blocks)
```

## 2. Whitepaper Reference

*   **Section:** 2.9 Safety
*   **Reference:** **Theorem 1 (safety)**.

**Theorem 1:** "If any correct node finalizes a block $b$ in slot $s$ and any correct node finalizes any block $b'$ in any slot $s' \geq s$, $b'$ is a descendant of $b$."

## 3. Reasoning and Analysis

This `SafetyInvariant` is the most critical safety property of the Alpenglow protocol. It guarantees that the finalized ledger is a single, non-forking chain. All correct nodes must agree on the total order of finalized blocks.

### Whitepaper Claim (Theorem 1)

Theorem 1 establishes the core safety guarantee: the set of all finalized blocks across all correct nodes constitutes a single, totally ordered chain. If you take any two finalized blocks, one must be an ancestor of the other. The theorem is phrased as: if block `b` is in slot `s` and block `b'` is in slot `s'` with `s <= s'`, then `b'` must be a descendant of `b`.

This prevents a situation where, for example, node A finalizes block `X` at slot 100, and node B finalizes a conflicting block `Y` at slot 100, or even a block at slot 101 that does not build on `X`.

### TLA+ Code Implementation

The TLA+ code is a direct and faithful formalization of Theorem 1:

*   `\A v1, v2 \in CorrectNodes`: It considers any pair of correct nodes.
*   `\A b1 \in finalized[v1], b2 \in finalized[v2]`: It considers any block `b1` finalized by the first node and any block `b2` finalized by the second node.
*   `(b1.slot <= b2.slot) => IsAncestor(b1, b2, blocks)`: This is the core assertion. It states that if `b1` occurred in a slot less than or equal to `b2`'s slot, then `b1` must be an ancestor of `b2`.
    *   The statement "`b'` is a descendant of `b`" from the whitepaper is equivalent to "`b` is an ancestor of `b'`".
    *   The `IsAncestor` function (defined in `Blocks.tla`) correctly implements the transitive parent-child relationship.

This logic precisely captures the single-chain property described in Theorem 1.

## 4. Conclusion

The `SafetyInvariant` TLA+ property is a **correct and accurate** formalization of the main safety guarantee (Theorem 1) of the Alpenglow protocol. It correctly asserts that the set of all finalized blocks forms a single, non-forking chain. The audit finds no correctness issues with this code.

## 5. Open Questions or Concerns

*   None. This is the lynchpin of the protocol's safety, and it is specified correctly.

## 6. Suggestions for Improvement

*   No improvements are suggested. The code is clear, and its name perfectly describes its critical role as the main safety invariant.