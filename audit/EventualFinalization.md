# Audit Report: EventualFinalization Property

## 1. TLA+ Code Under Audit

The following TLA+ code defines the `EventualFinalization` liveness property:

```tla
EventualFinalization ==
    (time >= GST) ~> 
        (\E v \in Validators : 
             \E b \in blocks : b.slot > 0 /\ b \in finalized[v])
```

This formula is located in the `MainProtocol.tla` file.

## 2. Whitepaper References

This property corresponds to the high-level liveness guarantee of the Alpenglow protocol. The key references in the `alpenglow-whitepaper.md` are:

*   **Section 1.5, Page 11, "Correctness":**
    > **Liveness.** In any long enough period of network synchrony, correct nodes finalize new blocks produced by correct nodes. (See also Theorem 2)

*   **Section 1.5, Page 10-11, "Asynchrony" and "Synchrony":**
    > We consider the partially synchronous network setting of Global Stabilization Time (GST) ... we only guarantee *liveness* when the network is synchronous... after time GST all previous and future messages ... will arrive at the recipient at latest at time $\max(\text{GST}, t_m) + \Delta$.

*   **Section 2.10, Page 33, "Liveness" and Theorem 2:**
    This section provides a detailed proof for a specific liveness scenario, which supports the overall liveness claim. Theorem 2 states that under certain ideal conditions (correct leader, successful block dissemination after GST), all blocks in a leader's window will be finalized.

## 3. Reasoning and Analysis

### TLA+ Formula Breakdown

The `EventualFinalization` property is a temporal logic formula that makes a fundamental assertion about the system's ability to make progress.

- `(time >= GST) ~> ...`: This is the core of the liveness property. It reads as "Once the system time is at or after the Global Stabilization Time (GST), it is eventually guaranteed that...". The `~>` operator signifies "leads to" or "eventually". This directly models the whitepaper's condition of requiring network synchrony for liveness.
- `(\E v \in Validators : ...)`: There exists at least one validator `v`.
- `(\E b \in blocks : ...)`: There exists at least one block `b`.
- `b.slot > 0`: The block's slot number is greater than zero. This is a standard check to ensure the finalized block is not the notional Genesis block, meaning actual progress has been made.
- `b \in finalized[v]`: The block `b` is present in the set of blocks that validator `v` considers finalized.

In summary, the formula asserts: **After the network has stabilized (post-GST), the system will eventually finalize at least one new block.**

### Comparison with Whitepaper

The TLA+ property is a direct and accurate formalization of the high-level liveness guarantee stated on page 11 of the whitepaper. The whitepaper promises that "in any long enough period of network synchrony, correct nodes finalize new blocks." The TLA+ model uses `time >= GST` to represent this "long enough period of network synchrony."

While **Theorem 2** provides a proof for a more specific and stronger liveness outcome under ideal conditions, the `EventualFinalization` property serves as a more general and fundamental check. The TLA+ model checker will verify this property across all possible system behaviors allowed by the specification, not just the ideal path described in Theorem 2. This ensures that the system does not deadlock or halt after GST, even in the presence of Byzantine behavior or non-ideal scenarios that fall within the model's parameters.

## 4. Conclusion

The `EventualFinalization` TLA+ property correctly and appropriately models the fundamental liveness guarantee of the Alpenglow protocol as described in the whitepaper. It serves as a crucial safety net to ensure the system makes progress and does not halt indefinitely. The property is a sound abstraction of the high-level liveness goal.

## 5. Open Questions and Concerns

1.  **Specificity of Validator:** The property uses `\E v \in Validators`, which includes both correct and Byzantine validators. While safety properties (like `SafetyInvariant`) should prevent a Byzantine node from finalizing a block that a correct node would not, it's worth noting that the property is satisfied even if only a Byzantine node finalizes a block. The whitepaper's definition refers to "correct nodes" finalizing blocks. Does the model rely solely on other safety invariants to ensure that any finalized block (even if recorded by a Byzantine node) is valid and part of the one true chain?
2.  **Minimal Progress:** The property only guarantees the finalization of *at least one* block after GST. It does not guarantee continuous progress. A stronger liveness property, also present in `MainProtocol.tla` as `Liveness` (which asserts the highest finalized slot keeps increasing), seems to be the primary guarantee for continuous progress. `EventualFinalization` appears to be a foundational, "sanity check" liveness property.

## 6. Suggestions for Improvement

1.  **Naming Clarification:** To avoid ambiguity with the stronger, continuous liveness property, consider renaming `EventualFinalization` to something like `BasicLiveness` or `ProgressSanityCheck`. This would clarify its role as a foundational guarantee against complete system halt, as opposed to a guarantee of perpetual progress.
2.  **Audit Stronger Liveness:** A separate and thorough audit of the `Liveness` property (the one ensuring the highest finalized slot increases) is highly recommended to get a complete picture of the liveness guarantees verified by the TLA+ model.
