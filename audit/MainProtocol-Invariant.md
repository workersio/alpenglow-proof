# Audit Report: MainProtocol Invariant

## 1. Code Under Audit

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

## 2. Whitepaper Section and References

The `Invariant` block represents the overall safety properties of the Alpenglow protocol. The most relevant section in the whitepaper is **Section 2.9 Safety**, which introduces the main safety theorem (Theorem 1) and a series of lemmas that build up to it.

- **Theorem 1 (Safety):** "If any correct node finalizes a block b in slot s and any correct node finalizes any block b' in any slot s' >= s, b' is a descendant of b." (Page 32)

The `Invariant` is a conjunction of multiple lower-level invariants, each corresponding to a specific safety property or lemma described in the whitepaper.

## 3. Reasoning and Analysis

The `Invariant` in `MainProtocol.tla` is the top-level safety property for the model. It is defined as a conjunction of several more specific invariants. This is a standard and effective way to structure TLA+ specifications, as it allows for checking individual properties separately and then combining them to prove the overall system safety.

Below is a breakdown of each component of the `Invariant` and its relation to the whitepaper:

- **`TypeInvariant`**: (L602 in `MainProtocol.tla`) This is a standard invariant in TLA+ models that ensures all variables remain within their expected types. It does not directly correspond to a specific concept in the whitepaper but is a fundamental part of ensuring model correctness.

- **`SafetyInvariant`**: (L447 in `MainProtocol.tla`) This directly corresponds to **Theorem 1** on page 32 of the whitepaper. It asserts that finalized blocks form a single, consistent chain.

- **`NoConflictingFinalization`**: (L456 in `MainProtocol.tla`) This is a direct corollary of Theorem 1, as stated in the comment in the TLA+ code. It ensures that two different blocks cannot be finalized in the same slot.

- **`ChainConsistency`**: (L465 in `MainProtocol.tla`) This is stated to be equivalent to `SafetyInvariant` and is likely included for clarity, possibly to match the naming in an earlier version of the specification or to emphasize the property under the specific Byzantine stake assumption.

- **`VoteUniqueness`**: (L471 in `MainProtocol.tla`) This corresponds to **Lemma 20** on page 28 of the whitepaper, which states that correct nodes cast at most one initial vote per slot.

- **`UniqueNotarization`**: (L483 in `MainProtocol.tla`) This corresponds to **Lemma 24** on page 29 of the whitepaper, which ensures that at most one block can be notarized per slot.

- **`GlobalNotarizationUniqueness`**: (L496 in `MainProtocol.tla`) This is a stronger, global version of `UniqueNotarization`, ensuring that all correct nodes agree on the notarized block for a given slot. This is also discussed in the context of Lemma 24.

- **`FinalizedImpliesNotarized`**: (L510 in `MainProtocol.tla`) This corresponds to **Lemma 25** on page 30 of the whitepaper, which states that a block must be notarized before it can be finalized.

- **`CertificateNonEquivocation`**: (L523 in `MainProtocol.tla`) This relates to the properties of certificates as described in **Definition 13** on page 20. It ensures a validator doesn't create conflicting certificates for the same slot and type.

- **`ByzantineStakeOK`**: (L80 in `MainProtocol.tla`) This invariant checks that the total stake of byzantine nodes is less than 20%, which is **Assumption 1** on page 4 of the whitepaper.

- **`PoolMultiplicityOK`** and **`PoolCertificateUniqueness`**: (L533-L536 in `MainProtocol.tla`) These invariants relate to the properties of the `Pool` data structure, as described in **Section 2.5 Pool** (page 20), particularly Definitions 12 and 13. They ensure that votes and certificates are stored correctly.

- **`RotorSelectSoundness`**: (L543 in `MainProtocol.tla`) This invariant ensures that the `RotorSelect` function behaves correctly, as described in **Section 2.2 Rotor** and **Section 3.1 Smart Sampling**.

## 4. Conclusion

The `Invariant` block in `MainProtocol.tla` is a comprehensive and well-structured representation of the safety properties of the Alpenglow protocol as described in the whitepaper. It correctly combines all the necessary sub-invariants to ensure the overall safety of the system. The naming of the sub-invariants is clear and maps well to the concepts and lemmas in the whitepaper.

## 5. Open Questions or Concerns

- The `ChainConsistency` invariant is currently defined as being identical to `SafetyInvariant`. While this is not incorrect, it might be worth clarifying in the comments why it is included as a separate item in the main `Invariant`. Is it for historical reasons, or to make it easier to check a property with a specific name?

## 6. Suggestions for Improvement

- While the comments in `MainProtocol.tla` are generally good, adding a brief, one-line comment next to each sub-invariant in the main `Invariant` block could improve readability for someone new to the specification. For example:

```tla
Invariant ==
    /\ TypeInvariant                \* Variables have the correct types
    /\ SafetyInvariant              \* Finalized blocks form a single chain (Theorem 1)
    /\ NoConflictingFinalization    \* No two different blocks finalized in the same slot
    ...
```
This would provide a quick reference without needing to navigate to the definition of each invariant.
