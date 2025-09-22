# Audit Report: StateConstraint

### 1. Code that you are auditing.
```tla
StateConstraint ==
    /\ Cardinality(blocks) <= MaxBlocks
    /\ time <= GST + 10
    /\ \A v \in Validators :
       \A s \in 1..MaxSlot :
           Cardinality(GetVotesForSlot(validators[v].pool, s)) <= NumValidators * 5
```

### 2. The whitepaper section and references that the code represents.

This code does not directly correspond to a specific theorem or definition in the whitepaper. Instead, it defines state constraints for the TLA+ model checker (TLC). These are practical limits imposed on the model to keep the state space finite and explorable by TLC within a reasonable amount of time and memory. The constants used (`MaxBlocks`, `GST`, `MaxSlot`, `NumValidators`) are parameters of the model, not the protocol itself.

### 3. The reasoning behind the code and what the whitepaper claims.

The purpose of a `StateConstraint` is to prevent the model checker from exploring an infinite or intractably large number of states. It prunes the search tree by telling TLC to ignore states that violate these bounds.

*   `Cardinality(blocks) <= MaxBlocks`: This limits the total number of block records that can be created in the system. This is essential because without a bound, leaders could propose an infinite number of blocks. `MaxBlocks` is a constant configured for the model run. This is a standard and necessary constraint for model checking any protocol that creates new objects.

*   `time <= GST + 10`: This limits how far the model's global `time` variable can advance. The limit is set relative to the `GST` (Global Stabilization Time) constant. This allows the model to explore behaviors both before and after GST, which is critical for checking liveness properties that only hold after GST. The "+ 10" provides a reasonable window of time after GST for the system to make progress. This is a reasonable approach to bounding time.

*   `\A v \in Validators : \A s \in 1..MaxSlot : Cardinality(GetVotesForSlot(validators[v].pool, s)) <= NumValidators * 5`: This is a constraint on the number of vote messages stored in a single validator's pool for a single slot. The whitepaper's `PoolMultiplicityOK` invariant (based on Definition 12) already provides a much tighter bound for the votes *from a single validator*. A single validator can store at most 1 `NotarVote`, 1 `SkipVote`, 3 `NotarFallbackVote`, 1 `SkipFallbackVote`, and 1 `FinalVote`, for a total of 7 votes *from a single source validator*. This constraint seems to be a global sanity check on the total number of votes a validator stores for a slot *from all sources*. The bound `NumValidators * 5` seems generous but reasonable, as it's unlikely to be hit in normal operation but prevents the state from exploding due to an unforeseen bug or a Byzantine node spamming votes (though even spam is limited by `PoolMultiplicityOK`).

### 4. The conclusion of the audit.

The `StateConstraint` property is **correct and appropriate** for its purpose, which is to enable bounded model checking with TLC. The constraints are logical and necessary to make the state space finite.

*   The block and time constraints are standard and well-reasoned.
*   The vote cardinality constraint is a reasonable safeguard against state space explosion, although the `PoolMultiplicityOK` invariant provides the primary, protocol-defined limit on vote storage.

These constraints do not represent properties of the Alpenglow protocol itself but are essential tools for verifying the protocol's properties with a model checker. There are no correctness issues with this code in the context of its intended use.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

*   The comment for the vote cardinality constraint could be slightly more descriptive, e.g., "Sanity check to bound the total number of votes stored per slot in a validator's pool."
