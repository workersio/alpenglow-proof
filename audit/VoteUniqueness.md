# Audit Report: VoteUniqueness

## 1. Code Under Audit

```tla
VoteUniqueness ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET votes == GetVotesForSlot(validators[v].pool, slot)
            initVotes == {vt \in votes : 
                         IsInitialVote(vt) /\ vt.validator = v}
        IN Cardinality(initVotes) <= 1
```

## 2. Whitepaper Reference

*   **Section:** 2.9 Safety
*   **Reference:** Lemma 20: "A correct node exclusively casts only one notarization vote or skip vote per slot."

## 3. Reasoning and Analysis

The `VoteUniqueness` property ensures that a correct validator does not equivocate by casting multiple initial votes within the same slot. This is a fundamental requirement for preventing ambiguity and ensuring that stake is counted correctly and uniquely.

### Whitepaper Claim (Lemma 20)

Lemma 20 states: "A correct node exclusively casts only one notarization vote or skip vote per slot."

The proof is based on the state machine logic in Algorithm 1 and 2:
1.  Initial votes (`NotarVote` or `SkipVote`) are cast by the `TRYNOTAR` and `TRYSKIPWINDOW` functions.
2.  Both of these functions are guarded by the condition `Voted \notin state[s]`, meaning a vote can only be cast if no initial vote has been cast before in that slot.
3.  Upon casting an initial vote, the `Voted` flag is immediately added to `state[s]`, preventing any subsequent initial votes in the same slot.

### TLA+ Code Implementation

The TLA+ code formalizes this behavior as a safety invariant:

*   `\A v \in CorrectNodes`: The property must hold for every correct validator.
*   `\A slot \in 1..MaxSlot`: The check is performed for every slot in the model.
*   `LET votes == GetVotesForSlot(validators[v].pool, slot)`: It retrieves all votes for a given slot from the validator's own pool.
*   `initVotes == {vt \in votes : IsInitialVote(vt) /\ vt.validator = v}`: This is the crucial step. It filters the collected votes to find only the *initial votes* that were cast by the validator `v` itself. The `IsInitialVote` operator, defined in `Messages.tla`, correctly identifies votes of type `NotarVote` or `SkipVote`.
*   `Cardinality(initVotes) <= 1`: The assertion checks that the set of initial votes from validator `v` for slot `s` contains at most one element.

This logic perfectly mirrors the claim in Lemma 20. It checks that a validator's pool never contains more than one of its own initial votes for any given slot, effectively checking for equivocation.

## 4. Conclusion

The `VoteUniqueness` TLA+ property is a **correct and accurate** formalization of the safety guarantee described in Lemma 20 of the Alpenglow whitepaper. The logic is sound and directly reflects the mechanisms described in the paper to prevent a correct node from voting twice. The audit finds no correctness issues with this code.

## 5. Open Questions or Concerns

*   None. The property is clearly defined, self-contained, and correctly implemented.

## 6. Suggestions for Improvement

*   No improvements are suggested. The code is clear, concise, and its name accurately reflects its purpose.