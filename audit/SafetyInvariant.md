# Audit Report: SafetyInvariant

### 1. Code that you are auditing.
```tla
SafetyInvariant ==
    /\ \A v1, v2 \in CorrectNodes:
        \A b1 \in finalized[v1], b2 \in finalized[v2]:
            (b1.slot <= b2.slot) => IsAncestor(b1, b2, blocks)
    /\ \A v1, v2 \in CorrectNodes:
        \A b1 \in finalized[v1], b2 \in finalized[v2]:
            (b1.slot = b2.slot) => (b1.hash = b2.hash)
```

### 2. The whitepaper section and references that the code represents.

This `SafetyInvariant` directly corresponds to **Theorem 1 (safety)** in the whitepaper (Section 2.9, page 32):

> **Theorem 1 (safety).** *If any correct node finalizes a block $b$ in slot $s$ and any correct node finalizes any block $b'$ in any slot $s' \geq s$, $b'$ is a descendant of $b$.*

The second part of the TLA+ code is a direct corollary of Theorem 1. If $s = s'$, then $b$ must be a descendant of $b'$ and $b'$ must be a descendant of $b$. This is only possible if $b$ and $b'$ are the same block.

### 3. The reasoning behind the code and what the whitepaper claims.

The `SafetyInvariant` is the most critical safety property of the Alpenglow protocol. It guarantees that the finalized ledger is a single, non-forking chain. All correct nodes must agree on the total order of finalized blocks.

*   **First Part:** `(b1.slot <= b2.slot) => IsAncestor(b1, b2, blocks)`
    *   This part of the invariant formalizes the main statement of Theorem 1. It states that if you take any two finalized blocks `b1` and `b2` from any two correct nodes `v1` and `v2`, and `b1` is in a slot less than or equal to `b2`'s slot, then `b1` must be an ancestor of `b2`.
    *   The `IsAncestor` function, defined in `Blocks.tla`, correctly implements the transitive parent-child relationship by recursively following parent hashes.
    *   This ensures that the finalized history is linear. A node cannot finalize a block at a later slot that doesn't build upon a block finalized at an earlier slot.

*   **Second Part:** `(b1.slot = b2.slot) => (b1.hash = b2.hash)`
    *   This is a critical consequence of the first part and is explicitly stated as a separate property for clarity and emphasis. It is also checked by the `NoConflictingFinalization` property in `MainProtocol.tla`.
    *   It asserts that if two correct nodes finalize blocks in the same slot, those blocks must be identical (have the same hash).
    *   This directly prevents forks at the same slot height, which is a fundamental requirement for a safe consensus protocol.

### 4. The conclusion of the audit.

The `SafetyInvariant` TLA+ property is a **correct and accurate** formalization of the main safety guarantee (Theorem 1) of the Alpenglow protocol. It correctly asserts that the set of all finalized blocks across all correct nodes forms a single, non-forking chain. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

The property is well-defined. For even greater clarity, the two parts of the conjunction could be given separate names, as is done in `MainProtocol.tla` with `SafetyInvariant` and `NoConflictingFinalization`. However, combining them under a single `SafetyInvariant` is also perfectly acceptable.
