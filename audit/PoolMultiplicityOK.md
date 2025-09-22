# Audit Report: PoolMultiplicityOK

### 1. Code that you are auditing.
```tla
PoolMultiplicityOK ==
    \A v \in Validators : MultiplicityRulesRespected(validators[v].pool)
```

### 2. The whitepaper section and references that the code represents.

This property directly corresponds to **Definition 12 (storing votes)** in Section 2.5 (page 20) of the whitepaper:

> **Definition 12 (storing votes).** *Pool stores received votes for every slot and every node as follows:*
>
> * The first received notarization or skip vote,
> * up to 3 received notar-fallback votes,
> * the first received skip-fallback vote, and
> * the first received finalization vote.

### 3. The reasoning behind the code and what the whitepaper claims.

The `PoolMultiplicityOK` property ensures that the vote storage rules defined in the whitepaper are never violated in any validator's pool. These rules are crucial for preventing certain types of attacks (like a single validator's vote being counted multiple times) and for managing the state of the `Pool`.

The TLA+ code breaks this down into two parts:
1.  `PoolMultiplicityOK`: This is the top-level invariant that iterates over all validators (`\A v \in Validators`) and applies the `MultiplicityRulesRespected` check to each validator's pool.
2.  `MultiplicityRulesRespected(pool)`: This helper predicate, defined in `VoteStorage.tla`, contains the actual logic. It iterates through each slot and validator within a given pool and checks the cardinality of each vote type, ensuring they do not exceed the limits set by Definition 12.

The `MultiplicityRulesRespected` predicate is defined as:
```tla
MultiplicityRulesRespected(pool) ==
    \A s \in Slots, v \in Validators :
        LET votes == pool.votes[s][v]
        IN /\ Cardinality({vt \in votes : vt.type = "NotarVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "SkipVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "NotarFallbackVote"}) <= 3
           /\ Cardinality({vt \in votes : vt.type = "SkipFallbackVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "FinalVote"}) <= 1
```
This is a direct and precise translation of the bullet points in Definition 12. The operational enforcement of this is done by the `CanStoreVote` predicate, which is checked before any vote is added to the pool by the `StoreVote` action. `PoolMultiplicityOK` is the invariant that confirms this mechanism works correctly in all reachable states.

A key point from the whitepaper is "The first received notarization or skip vote". The TLA+ code in `CanStoreVote` currently checks for `NotarVote` and `SkipVote` uniqueness independently. This is a slight, but important, deviation. A malicious or faulty node could send both a `NotarVote` and a `SkipVote` for the same slot, and both would be stored, violating the "or" condition. While `VoteUniqueness` ensures a *correct* node won't do this, the pool should ideally reject such equivocation from any node.

### 4. The conclusion of the audit.

The `PoolMultiplicityOK` TLA+ property, via its helper `MultiplicityRulesRespected`, correctly formalizes most of the vote storage multiplicity rules from Definition 12 of the Alpenglow whitepaper.

However, there is a **minor discrepancy**. The whitepaper states "The first received notarization **or** skip vote," implying mutual exclusion. The current implementation in `CanStoreVote` allows one of *each* to be stored. This could allow a Byzantine validator to have its stake counted towards both notarization and skip totals in the same slot, which could have subtle effects on the fallback logic. While other parts of the specification (like `VoteUniqueness` for correct nodes and stake counting logic) mitigate the impact, it's a deviation from the strict letter of the whitepaper.

### 5. Any open questions or concerns.

*   Does the potential for a Byzantine node to have both a `NotarVote` and `SkipVote` stored in a pool create any vulnerability in the fallback event logic (`CanEmitSafeToNotar`, `CanEmitSafeToSkip`)? The stake counting helpers (`TotalNotarStake`, `SkipStake`) seem to count validators uniquely within their respective vote types, but a validator could contribute to both totals simultaneously. This seems to violate the "count once per slot" principle mentioned in Definition 16.

### 6. Any suggestions for improvement.

*   The `CanStoreVote` predicate in `VoteStorage.tla` should be updated to enforce mutual exclusion between `NotarVote` and `SkipVote` for the same validator and slot. For example:
    *   When checking if a `NotarVote` can be stored, also check that no `SkipVote` exists from that validator for that slot.
    *   When checking if a `SkipVote` can be stored, also check that no `NotarVote` exists.

This change would bring the TLA+ model into closer alignment with the strict interpretation of Definition 12.
