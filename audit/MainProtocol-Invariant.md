# Audit Report: Main Protocol Invariant

### 1. Code that you are auditing.
```tla
Invariant ==
    /\ TypeInvariant
    /\ SafetyInvariant
    /\ NoConflictingFinalization
    /\ ChainConsistency
    /\ VoteUniqueness
    /\ UniqueNotarization
    /\ GlobalNotarizationUniqueness
    /\ FinalizedImpliesNotarized
    /\ CertificateNonEquivocation
    /\ ByzantineStakeOK
    /\ PoolMultiplicityOK
    /\ PoolCertificateUniqueness
    /\ RotorSelectSoundness
```

### 2. The whitepaper section and references that the code represents.

This `Invariant` is the top-level safety property for the entire Alpenglow specification. It combines numerous individual invariants that correspond to a wide range of definitions, lemmas, and theorems throughout the whitepaper, primarily in **Section 2.9 (Safety)** and **Section 2.5 (Pool)**. Its main goal is to assert that all fundamental safety guarantees hold in every reachable state of the model.

### 3. The reasoning behind the code and what the whitepaper claims.

The `Invariant` operator combines all the critical safety properties of the system into a single predicate. The TLA+ model checker (TLC) will check that this property holds true in every single state it explores, starting from the `Init` state. If `Invariant` is ever violated, it means a safety property has been broken.

Each component of the conjunction has been audited separately:
*   **`TypeInvariant`**: Ensures all state variables have the correct types. (See `audit/TypeInvariant.md`)
*   **`SafetyInvariant`**: Ensures finalized blocks form a single, non-forking ancestral chain, corresponding to **Theorem 1**. (See `audit/SafetyInvariant.md`)
*   **`NoConflictingFinalization`**: A corollary of Theorem 1, ensuring two different blocks are never finalized in the same slot. (See `audit/NoConflictingFinalization.md`)
*   **`ChainConsistency`**: An alias for `SafetyInvariant`, providing a more descriptive name for the core safety guarantee. (See `audit/ChainConsistency.md`)
*   **`VoteUniqueness`**: Ensures a correct node casts at most one initial vote per slot, corresponding to **Lemma 20**. (See `audit/VoteUniqueness.md`)
*   **`UniqueNotarization`**: Ensures a correct node's pool contains notarization certificates for at most one block per slot, corresponding to **Lemma 24**. (See `audit/UniqueNotarization.md`)
*   **`GlobalNotarizationUniqueness`**: Extends `UniqueNotarization` to ensure all correct nodes agree on the same single notarized block per slot. (See `audit/GlobalNotarizationUniqueness.md`)
*   **`FinalizedImpliesNotarized`**: Ensures any finalized block was first notarized, corresponding to **Lemma 25**. (See `audit/FinalizedImpliesNotarized.md`)
*   **`CertificateNonEquivocation`**: Ensures a correct node's pool does not contain conflicting certificates of the same type for the same slot, corresponding to **Definition 13**. (See `audit/CertificateNonEquivocation.md`)
*   **`ByzantineStakeOK`**: Enforces the core assumption that byzantine stake is less than 20%, corresponding to **Assumption 1**. (See `audit/ByzantineStakeOK.md`)
*   **`PoolMultiplicityOK`**: Ensures vote storage counts in every validator's pool respect the rules of **Definition 12**. (See `audit/PoolMultiplicityOK.md`)
*   **`PoolCertificateUniqueness`**: Ensures certificate storage in every validator's pool respects the uniqueness rules of **Definition 13**. (See `audit/PoolCertificateUniqueness.md`)
*   **`RotorSelectSoundness`**: Checks that the Rotor relay selection mechanism is sound. (See `audit/RotorSelectSoundness.md`)

### 4. The conclusion of the audit.

The main `Invariant` provides comprehensive safety coverage for the Alpenglow protocol, formalizing the key theorems, lemmas, and definitions from the whitepaper. The individual components are logically sound and, when combined, create a strong assertion about the overall safety of the system.

However, the audit of the individual components has revealed two issues that affect the overall integrity of this main `Invariant`:

1.  **Major Issue in `RotorSelectSoundness`**: There is a fundamental inconsistency in how Rotor relay selection is checked. The soundness check uses a legacy set-based model (`StructuralOK`) while the feasibility check uses a modern bin-based model (`RotorBinAssignmentPossible`). This makes the `RotorSelectSoundness` invariant unreliable.
2.  **Minor Issue in `PoolMultiplicityOK`**: There is a slight deviation from the whitepaper's rule for storing initial votes. The spec allows storing one `NotarVote` AND one `SkipVote` from the same validator in the same slot, whereas Definition 12 implies mutual exclusion ("notarization **or** skip vote").

Because the main `Invariant` is a conjunction of all these properties, the issues in the sub-properties mean that the main `Invariant` itself is not as strong or correct as it could be. The `RotorSelectSoundness` issue is particularly concerning as it points to a potential logic error in the specification of a critical component.

### 5. Any open questions or concerns.

*   The primary concern is the inconsistent modeling in the Rotor specification. This should be resolved to ensure the model is internally consistent and accurately reflects the intended design.
*   The secondary concern is the slight deviation in vote multiplicity rules, which could have unintended consequences for the fallback logic under adversarial conditions.

### 6. Any suggestions for improvement.

The suggestions from the individual audit reports are summarized here:

*   **High Priority:** Refactor the `Rotor.tla` module to **consistently use the bin-based model** for all checks related to relay selection, including updating `RotorSelectSound` to use `StructuralBinOK`.
*   **Medium Priority:** Update the `CanStoreVote` predicate in `VoteStorage.tla` to enforce **mutual exclusion** between `NotarVote` and `SkipVote` from the same validator in the same slot, to align perfectly with Definition 12.

Fixing these two issues would resolve the identified discrepancies and significantly strengthen the correctness guarantee provided by the main `Invariant`.