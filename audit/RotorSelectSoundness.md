# Audit Report: RotorSelectSoundness

This report audits the TLA+ code block for `RotorSelectSoundness` against the Alpenglow whitepaper.

## 1. Code Under Audit

```tla
RotorSelectSoundness ==
    \A b \in blocks :
        LET needers == {v \in Validators : b \notin blockAvailability[v]}
            nextSlot == IF b.slot + 1 <= MaxSlot THEN b.slot + 1 ELSE b.slot
            nextLeader == Leader(nextSlot)
        IN RotorSelectSound(b, needers, nextLeader)
```

The property relies on the following definition from `Rotor.tla`:
```tla
RotorSelectSound(block, needers, nextLeader) ==
    LET sel == RotorSelect(block, needers, nextLeader)
    IN (sel # {} => StructuralOK(sel, needers, nextLeader))
       /\ (needers # {} /\ ~RotorBinAssignmentPossible(block, needers, nextLeader) => sel = {})
```

## 2. Whitepaper References

The audited code represents the soundness of the **Rotor** block dissemination mechanism, which is primarily described in two sections of the whitepaper:

*   **Section 2.2 "Rotor" (Page 15):** Describes the high-level function of Rotor, including its use of relay nodes to disseminate erasure-coded shreds. It states:
    > "Each relay then broadcasts its shred to all nodes that still need it..."
    > "As a minor optimization, all shred relays send their shred to the next leader first."

*   **Section 3.1 "Smart Sampling" (Page 40):** Details the **Partition Sampling (PS-P)** algorithm (**Definition 46**) used to select the relay nodes. Key aspects include:
    1.  **Deterministic Inclusion:** "For each node with relative stake ρᵢ > 1/Γ, fill ⌊ρᵢΓ⌋ bins with that node." This implies large stakeholders are guaranteed inclusion.
    2.  **Proportional Sampling:** "From each bin, sample one node proportional to their stake."

## 3. Reasoning and Analysis

The `RotorSelectSoundness` property is a safety invariant that asserts that for any given block, the selection of relay nodes by the Rotor mechanism is always correct according to the rules specified in the TLA+ model.

1.  **`needers` variable:** The TLA+ expression `LET needers == {v \in Validators : b \notin blockAvailability[v]}` is a direct and accurate formalization of the whitepaper's concept of "nodes that still need" a block.

2.  **`nextLeader` variable:** The code correctly identifies the leader of the subsequent slot and passes it to the selection logic. This directly maps to the "send to the next leader first" optimization mentioned in Section 2.2.

3.  **`RotorSelectSound` Predicate:** This is the core of the logic and has two parts:
    *   **`sel # {} => StructuralOK(sel, needers, nextLeader)`**: This clause asserts that if the relay selection process (`RotorSelect`) returns a non-empty set, that set must be "structurally okay". The `StructuralOK` predicate (defined in `Rotor.tla`) checks conditions that directly correspond to the whitepaper's requirements: the selected relays must be a subset of `needers`, must include large stakeholders, and must include the `nextLeader` if they are a needer. This correctly models the soundness of a successful selection.
    *   **`needers # {} /\ ~RotorBinAssignmentPossible(...) => sel = {}`**: This clause handles the failure case. It states that if there are nodes that need the block but it's impossible to form a valid set of relays (e.g., due to insufficient stake or number of available needers), the selection function *must* return an empty set. This is a critical safety feature. While not explicitly stated in the whitepaper in these terms, it is a fundamental requirement for a robust implementation. It ensures the protocol either uses a correct relay set or explicitly fails, preventing progression with a potentially insecure configuration.

## 4. Conclusion

The `RotorSelectSoundness` TLA+ property **accurately and robustly models** the principles of the Rotor relay selection mechanism as described in the Alpenglow whitepaper. It correctly captures the definition of nodes needing a block, the latency optimization for the next leader, the inclusion of large stakeholders from the PS-P sampling algorithm, and provides a crucial safety guarantee by ensuring the selection process fails cleanly when a valid relay set cannot be formed.

## 5. Open Questions and Concerns

1.  **Legacy vs. Modern Predicates:** The `Rotor.tla` file defines both a "legacy" set-based predicate `StructuralOK` and a more modern, bin-based predicate `StructuralBinOK`. The audited property, `RotorSelectSound`, uses the **legacy `StructuralOK`** for its checks. However, the feasibility check `RotorBinAssignmentPossible` uses the modern `BinCandidates` which relies on `StructuralBinOK`. This inconsistency is a significant concern. Why is the soundness invariant being checked against a legacy definition while the feasibility check uses the modern one? This could lead to scenarios where a selection is deemed feasible but fails the legacy soundness check, or vice-versa.

## 6. Suggestions for Improvement

1.  **Unify on the Bin-Based Model:** The specification should be refactored to **consistently use the bin-based model** across all related functions. The `RotorSelectSound` predicate should be updated to check against `StructuralBinOK` to align with the `RotorBinAssignmentPossible` feasibility check and the whitepaper's description of a bin-based sampling model. This would eliminate ambiguity and reduce the risk of subtle bugs arising from the conflicting models. For example, the property should be redefined to check the properties of the *bin assignment* itself, not the legacy set-based `sel`.
```