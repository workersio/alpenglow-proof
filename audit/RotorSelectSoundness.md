# Audit Report: RotorSelectSoundness

### 1. Code that you are auditing.
```tla
RotorSelectSoundness ==
    \A b \in blocks :
        LET needers == {v \in Validators : b \notin blockAvailability[v]}
            nextSlot == IF b.slot + 1 <= MaxSlot THEN b.slot + 1 ELSE b.slot
            nextLeader == Leader(nextSlot)
        IN RotorSelectSound(b, needers, nextLeader)
```
Helper predicate from `Rotor.tla`:
```tla
RotorSelectSound(block, needers, nextLeader) ==
    LET sel == RotorSelect(block, needers, nextLeader)
    IN (sel # {} => StructuralOK(sel, needers, nextLeader))
       /\ (needers # {} /\ ~RotorBinAssignmentPossible(block, needers, nextLeader) => sel = {})
```

### 2. The whitepaper section and references that the code represents.

This property relates to the Rotor block dissemination mechanism, described in **Section 2.2 "Rotor"** (pages 15-18) and the relay sampling algorithm in **Section 3.1 "Smart Sampling"** (page 40), which introduces the Partition Sampling (PS-P) algorithm. The property aims to ensure that the relay selection process is "sound" – meaning it follows the specified rules.

### 3. The reasoning behind the code and what the whitepaper claims.

The `RotorSelectSoundness` property is a safety invariant that asserts that for any given block, the selection of relay nodes by the Rotor mechanism is always correct according to the rules specified in the TLA+ model.

The logic is as follows:
1.  `needers`: The set of validators that do not have the block `b` available. This correctly models the nodes that need to receive the block.
2.  `nextLeader`: The leader of the next slot is calculated to give them priority in dissemination, which is a latency optimization mentioned in the whitepaper ("all shred relays send their shred to the next leader first").
3.  `RotorSelectSound` Predicate: This is the core of the logic and has two parts:
    *   `(sel # {} => StructuralOK(sel, needers, nextLeader))`: If the `RotorSelect` function returns a non-empty set of relays, that set must be structurally okay. `StructuralOK` checks that the relays are a subset of the needers, includes large stakeholders, and includes the next leader if needed. This is a simplified check for the PS-P algorithm.
    *   `(needers # {} /\ ~RotorBinAssignmentPossible(...) => sel = {})`: This clause handles the failure case. It states that if there are nodes that need the block but it's impossible to form a valid set of relays (according to the more modern, bin-based `RotorBinAssignmentPossible` predicate), the selection function *must* return an empty set. This is a critical safety feature to ensure the protocol either uses a correct relay set or explicitly fails.

### 4. The conclusion of the audit.

The `RotorSelectSoundness` TLA+ property attempts to model the principles of the Rotor relay selection mechanism. However, there is a **major inconsistency** in its implementation.

The property checks the soundness of the selection (`sel`) against a **legacy, set-based predicate (`StructuralOK`)**, while the feasibility of the selection is checked using a **modern, bin-based predicate (`RotorBinAssignmentPossible` which uses `StructuralBinOK`)**.

This is a significant issue because the two models for checking structural correctness are different. The bin-based model (`StructuralBinOK`) is a more accurate representation of the PS-P sampling algorithm described in the whitepaper, as it correctly handles the multiplicity of relays (a single large stakeholder can be chosen as a relay for multiple shreds). The set-based model (`StructuralOK`) is a simplification that loses this nuance.

Because the soundness check and the feasibility check use different underlying models, the invariant is not internally consistent. It's possible for a selection to be considered feasible by the bin-based model but fail the soundness check of the set-based model, or vice-versa. This makes the invariant unreliable.

### 5. Any open questions or concerns.

*   Why does the specification maintain two different models (set-based and bin-based) for Rotor's structural correctness?
*   Was the `RotorSelectSound` invariant intended to be updated to use the bin-based model but was missed?

### 6. Any suggestions for improvement.

*   **Unify on the Bin-Based Model:** The specification should be refactored to **consistently use the bin-based model** across all related functions. The `RotorSelectSound` predicate should be updated to check against `StructuralBinOK` to align with the `RotorBinAssignmentPossible` feasibility check and the whitepaper's description of a bin-based sampling model. This would eliminate ambiguity and reduce the risk of subtle bugs arising from the conflicting models.
*   The `StructuralOK` predicate and other legacy set-based helpers should be deprecated or removed to avoid confusion.
