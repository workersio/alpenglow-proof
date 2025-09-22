# Audit Report: NoConflictingFinalization

### 1. Code that you are auditing.
```tla
NoConflictingFinalization ==
    \A v1, v2 \in CorrectNodes:
        \A b1 \in finalized[v1], b2 \in finalized[v2]:
            (b1.slot = b2.slot) => (b1.hash = b2.hash)
```

### 2. The whitepaper section and references that the code represents.

This property is a direct corollary of **Theorem 1 (safety)** from Section 2.9 (page 32) of the whitepaper. While Theorem 1 states the broader property of a single ancestral chain, this invariant captures the most immediate and critical consequence: no two different blocks can be finalized in the same slot.

The `MainProtocol.tla` file explicitly links this property to Theorem 1:
```tla
(***************************************************************************
 * No conflicting finalization (Corollary of Theorem 1): if two validators
 * finalize blocks in the same slot, they must be identical.
 ***************************************************************************)
```

### 3. The reasoning behind the code and what the whitepaper claims.

The whitepaper's Theorem 1 guarantees that the set of all finalized blocks forms a single, linear chain of ancestry. A direct and critical consequence of this is that two distinct blocks cannot exist at the same height (slot). If two blocks, `b1` and `b2`, were finalized in the same slot (`b1.slot = b2.slot`) but had different hashes (`b1.hash != b2.hash`), then neither could be an ancestor of the other. This would violate the single-chain property guaranteed by Theorem 1.

The TLA+ code formalizes this reasoning directly:
*   `\A v1, v2 \in CorrectNodes`: It considers any two correct nodes.
*   `\A b1 \in finalized[v1], b2 \in finalized[v2]`: It considers any block `b1` finalized by the first node and any block `b2` finalized by the second node.
*   `(b1.slot = b2.slot) => b1.hash = b2.hash`: This is the core assertion. It states that if block `b1` and block `b2` are for the same slot, then they must have the same hash. This elegantly captures the impossibility of finalizing conflicting blocks.

This property is also the second conjunct of the `SafetyInvariant` property I just audited. Separating it into its own named invariant improves readability and allows for more granular checking during model checking.

### 4. The conclusion of the audit.

The `NoConflictingFinalization` TLA+ property is a **correct and accurate** formalization of a key safety guarantee that is a direct consequence of Theorem 1 in the Alpenglow whitepaper. It properly ensures that no two distinct blocks can be finalized in the same slot. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

None. The property is clear, concise, and correctly specified.
