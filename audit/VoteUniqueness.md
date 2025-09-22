# Audit Report: VoteUniqueness

### 1. Code that you are auditing.
```tla
VoteUniqueness ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET votes == GetVotesForSlot(validators[v].pool, slot)
            initVotes == {vt \in votes : 
                         IsInitialVote(vt) /\ vt.validator = v}
        IN Cardinality(initVotes) <= 1
```

### 2. The whitepaper section and references that the code represents.

This property directly corresponds to **Lemma 20 (notarization or skip)** in Section 2.9 (page 28) of the whitepaper:

> **Lemma 20 (notarization or skip).** A correct node exclusively casts only one notarization vote or skip vote per slot.

The proof of this lemma in the whitepaper relies on the `Voted` state in Algorithm 2, which is set after a correct node casts its first vote (either notarization or skip) in a slot, preventing it from casting another initial vote in the same slot.

### 3. The reasoning behind the code and what the whitepaper claims.

The `VoteUniqueness` property ensures that a correct validator does not equivocate by casting multiple initial votes (`NotarVote` or `SkipVote`) within the same slot. This is a fundamental safety requirement for preventing ambiguity and ensuring that stake is counted correctly and uniquely.

The TLA+ code formalizes this by:
1.  Iterating through each `CorrectNode` `v` and each `slot`.
2.  `LET votes == GetVotesForSlot(validators[v].pool, slot)`: It retrieves all votes for a given `slot` from the validator's own pool.
3.  `initVotes == {vt \in votes : IsInitialVote(vt) /\ vt.validator = v}`: This is the crucial step. It filters the collected votes to find only the *initial votes* (`NotarVote` or `SkipVote`) that were cast by the validator `v` itself.
4.  `IN Cardinality(initVotes) <= 1`: The assertion checks that the set of initial votes from validator `v` for slot `s` contains at most one element.

This logic perfectly mirrors the claim in Lemma 20. It checks that a validator's pool never contains more than one of its own initial votes for any given slot, effectively checking for equivocation. The underlying mechanism for this in the TLA+ spec is the `Voted` flag in `VotorCore.tla`, which is checked before casting an initial vote in `TryNotar` and `TrySkipWindow`.

### 4. The conclusion of the audit.

The `VoteUniqueness` TLA+ property is a **correct and accurate** formalization of the safety guarantee described in Lemma 20 of the Alpenglow whitepaper. The logic is sound and directly reflects the mechanisms described in the paper to prevent a correct node from voting twice. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

None. The property is well-defined and clearly expressed.
