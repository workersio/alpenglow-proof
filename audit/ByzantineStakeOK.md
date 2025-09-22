# Audit Report: ByzantineStakeOK

### 1. Code that you are auditing.
```tla
ByzantineStakeOK ==
    ByzantineStake * 100 < TotalStake * 20
```

### 2. The whitepaper section and references that the code represents.

This property directly corresponds to **Assumption 1 (fault tolerance)** in Section 1.2 (page 4) of the whitepaper:

> **Assumption 1 (fault tolerance).** *Byzantine nodes control less than 20% of the stake. The remaining nodes controlling more than 80% of stake are correct.*

### 3. The reasoning behind the code and what the whitepaper claims.

The `ByzantineStakeOK` property is a fundamental assumption of the Alpenglow protocol's safety and liveness arguments. It limits the power of the adversary. Many of the stake-based thresholds in the protocol (e.g., 60% for notarization, 80% for fast finalization) are chosen specifically based on this assumption.

The TLA+ code formalizes this assumption with a simple integer arithmetic check:
*   `ByzantineStake` calculates the sum of the stake of all nodes in the `byzantineNodes` set.
*   `TotalStake` calculates the sum of the stake of all validators in the system.
*   The expression `ByzantineStake * 100 < TotalStake * 20` is equivalent to `ByzantineStake / TotalStake < 0.20`, which is exactly what the whitepaper states: the byzantine stake is strictly less than 20% of the total stake.

This property is checked in the `Init` state predicate and as part of the main `Invariant`. This ensures that the model only explores states that adhere to this fundamental assumption.

### 4. The conclusion of the audit.

The `ByzantineStakeOK` TLA+ property is a **correct and accurate** formalization of Assumption 1 from the Alpenglow whitepaper. It correctly models the core resilience assumption that the total stake of byzantine nodes is strictly less than 20%. The audit finds no correctness issues with this code.

### 5. Any open questions or concerns.

None.

### 6. Any suggestions for improvement.

None. The property is a clear and direct translation of the assumption in the whitepaper.
