# Alpenglow Theorem 1: Lean Proof

This directory contains a simplified Lean 4 formalization and proof of Theorem 1 from the Alpenglow whitepaper.

## Theorem 1 (Safety)

**Statement**: If any correct node finalizes a block `b` in slot `s`, and any correct node finalizes any block `b'` in slot `s'` where `s ≤ s'`, then `b'` is a descendant of `b`.

**Significance**: This theorem ensures that once a block is finalized, all future finalized blocks must extend from it, preventing forks in the finalized chain. This is the core safety property of the Alpenglow consensus protocol.

## File Structure

### [Theorem1.lean](Theorem1.lean)

The main Lean file containing:

1. **Basic Types**
   - `Block`: Represents a blockchain block
   - `Slot`: Represents a time slot with a natural number
   - `LeaderWindow`: Represents a sequence of consecutive slots controlled by one leader

2. **Key Axioms** (simplified from the whitepaper)
   - `isDescendant`: Descendant relation between blocks
   - `isNotarized`: Block has received enough votes (60%+ stake)
   - `isFinalized`: Block is finalized (fast or slow finalization)
   - `slotOf`: Maps each block to its slot

3. **Lemmas from the Whitepaper**
   - **Lemma 25**: Finalized implies notarized
   - **Lemma 21 & 26**: Uniqueness of finalized blocks in a slot
   - **Lemma 31**: Same window safety
   - **Lemma 32**: Different window safety

4. **Main Theorem**
   - `alpenglow_safety`: The formal proof of Theorem 1

5. **Corollaries**
   - `finalized_blocks_form_chain`: Finalized blocks form a total order
   - `no_fork_in_slot`: No two different blocks can be finalized in the same slot
   - `no_fork_between_finalized`: No forks can occur between finalized blocks

## Proof Structure

The proof of Theorem 1 follows this logical structure:

```
Given: b finalized in slot s, b' finalized in slot s' where s ≤ s'
Goal: Prove b' is a descendant of b

Step 1: Apply Lemma 25
  → b' is notarized (since it's finalized)

Step 2: Case analysis on s vs s'

  Case 2a: s = s' (same slot)
    → By uniqueness (Lemmas 21 & 26), b = b'
    → b' is trivially a descendant of itself (reflexivity)

  Case 2b: s < s' (different slots)
    → Get unique leader windows for each slot

    Sub-case 2b.i: Same leader window
      → Apply Lemma 31 (same window safety)
      → b' is a descendant of b

    Sub-case 2b.ii: Different leader windows
      → Apply Lemma 32 (different window safety)
      → b' is a descendant of b

QED
```

## Simplifications

This formalization makes several simplifications compared to a full implementation:

1. **Axiomatized Predicates**: `isDescendant`, `isNotarized`, and `isFinalized` are axiomatized rather than fully defined
2. **Simplified Lemmas**: The key lemmas (25, 31, 32) are assumed as axioms rather than proven from first principles
3. **No Stake Model**: Byzantine stake assumptions are implicit in the lemmas
4. **No Vote Details**: The voting and certificate mechanisms are abstracted away

## Key Insights

The proof demonstrates that Alpenglow's safety comes from two mechanisms:

1. **Within Leader Windows** (Lemma 31)
   - Correct nodes vote for complete chains within a window
   - If one block is finalized, all later blocks in that window must build on it

2. **Across Leader Windows** (Lemma 32)
   - New windows must build on notarized blocks from previous windows (ParentReady requirement)
   - This creates a chain across windows that respects finalization

## How to Verify

To check that the proof is valid:

```bash
lean Theorem1.lean
```

This will:
- Type-check the entire file
- Verify all proofs are complete
- Output the theorem statements

Expected output:
```
alpenglow_safety (b b' : Block) : isFinalized b → isFinalized b' → slotOf b ≤ slotOf b' → isDescendant b' b
finalized_blocks_form_chain (b1 b2 : Block) : isFinalized b1 → isFinalized b2 → isDescendant b1 b2 ∨ isDescendant b2 b1
no_fork_in_slot (b1 b2 : Block) : isFinalized b1 → isFinalized b2 → slotOf b1 = slotOf b2 → b1 = b2
no_fork_between_finalized ...
```

## Dependencies

- Lean 4.23.0 (or later)
- No external libraries required (Mathlib imports are commented out)

## Future Work

To make this a complete formal verification, one could:

1. Define the parent relationship and derive `isDescendant` from it
2. Model the voting system and stake distribution
3. Prove Lemmas 21, 25, 31, and 32 from first principles
4. Model the complete protocol algorithms
5. Prove Theorem 2 (Liveness)
6. Connect to a certified execution model

## References

- Alpenglow Whitepaper: `../alpenglow-whitepaper.md`
- Theorem 1 appears on page 32 of the whitepaper
- Supporting lemmas appear on pages 29-32
