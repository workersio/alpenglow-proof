# Audit Report: TypeInvariant

### 1. Code that you are auditing.
```tla
TypeInvariant ==
    /\ validators \in [Validators -> ValidatorState]
    /\ blocks \subseteq Block
    /\ messages \subseteq (Vote \union Certificate)
    /\ byzantineNodes \subseteq Validators
    /\ time \in Nat
    /\ finalized \in [Validators -> SUBSET blocks]
    /\ blockAvailability \in [Validators -> SUBSET blocks]
    /\ \A v \in Validators : ValidatorStateOK(validators[v])
```

### 2. The whitepaper section and references that the code represents.

The `TypeInvariant` defines the global state of the Alpenglow protocol. The whitepaper describes these components across several sections:

*   **Validators (`validators`)**: Section 1.5, "Node" (page 8), describes the nodes (validators) participating in the protocol. The state of each validator (`ValidatorState`) is implicitly defined by the actions they can take, as described in Section 2.6 "Votor" (page 22) and Definition 18 (page 23).
*   **Blocks (`blocks`)**: Section 2.1, "Shred, Slice, Block" (page 14), particularly Definition 3 (page 15), defines the structure of a block.
*   **Messages (`messages`)**: Section 2.4, "Votes and Certificates" (page 19), defines the two types of messages in the system: `Vote` and `Certificate`.
*   **Byzantine Nodes (`byzantineNodes`)**: Section 1.5, "Adversary" (page 10), and Assumption 1 (page 4) describe the presence of byzantine nodes.
*   **Time (`time`)**: Section 1.5, "Time" and "Timeout" (pages 9-10), and Section 2.6, Definition 17 (page 23) describe the concept of time and timeouts.
*   **Finalized Blocks (`finalized`)**: Section 1.5, "Correctness" (page 11), and Section 2.5, Definition 14 (page 21) define block finalization.
*   **Block Availability (`blockAvailability`)**: Section 2.3, "Blokstor" (page 19), describes how blocks are stored and become available to nodes.
*   **Validator State OK (`ValidatorStateOK`)**: This is a TLA+ construct to ensure the internal consistency of each validator's state, which is an aggregation of the concepts in Section 2.6 "Votor".

### 3. The reasoning behind the code and what the whitepaper claims.

The `TypeInvariant` is a fundamental safety property in TLA+ that ensures the state variables of the specification always have the correct types. It's a sanity check that prevents the model from reaching nonsensical states.

*   `validators \in [Validators -> ValidatorState]`: This asserts that the `validators` variable is a function mapping each validator identifier to its corresponding `ValidatorState`. This correctly models that each validator has its own local state, as described in the whitepaper.
*   `blocks \subseteq Block`: This asserts that the `blocks` variable is a set of `Block` records. This correctly models the set of all blocks that have been created in the system.
*   `messages \subseteq (Vote \union Certificate)`: This asserts that the `messages` variable, representing the network, contains only `Vote` or `Certificate` messages. This aligns with Section 2.4 of the whitepaper.
*   `byzantineNodes \subseteq Validators`: This asserts that the set of byzantine nodes is a subset of all validators, which is consistent with the adversary model in the whitepaper.
*   `time \in Nat`: This asserts that `time` is a natural number, modeling the discrete progression of time.
*   `finalized \in [Validators -> SUBSET blocks]`: This asserts that `finalized` is a function mapping each validator to a set of blocks it has finalized. This correctly models that finalization is a local state for each validator.
*   `blockAvailability \in [Validators -> SUBSET blocks]`: This asserts that `blockAvailability` is a function mapping each validator to the set of blocks it has available locally. This corresponds to the Blokstor concept in the whitepaper.
*   `\A v \in Validators : ValidatorStateOK(validators[v])`: This asserts that for every validator, its internal state is consistent. This is a crucial check to ensure that the local state of each validator doesn't become corrupted.

### 4. The conclusion of the audit.

The `TypeInvariant` TLA+ code is a **correct and accurate** formalization of the global state of the Alpenglow protocol as described in the whitepaper. It correctly defines the types of all state variables and ensures their consistency throughout the execution of the model. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

None. This is a standard and well-formed type invariant.
