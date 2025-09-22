# Audit Report: `WindowFinalization` Liveness Property

## 1. Code Under Audit

The following TLA+ code from `MainProtocol.tla` is being audited:

```tla
WindowFinalization(s) ==
    (IsFirstSlotOfWindow(s) /\ Leader(s) \in CorrectNodes /\ NoTimeoutsBeforeGST(s) /\ time >= GST) ~>
        WindowFinalizedState(s)
```

## 2. Whitepaper Section and References

This TLA+ property directly corresponds to **Theorem 2 (Liveness)** from the Alpenglow whitepaper (Section 2.10, page 36).

**Theorem 2 (Liveness):**
> Let v_l be a correct leader of a leader window beginning with slot s. Suppose no correct node set the timeouts for slots in WINDOWSLOTS(s) before GST, and that Rotor is successful for all slots in WINDOWSLOTS(s). Then, blocks produced by v_l in all slots WINDOWSLOTS(s) will be finalized by all correct nodes.

The components of the TLA+ formula map to the theorem's premises as follows:

-   `IsFirstSlotOfWindow(s)`: Corresponds to "a leader window beginning with slot s".
-   `Leader(s) \in CorrectNodes`: Corresponds to "v_l be a correct leader".
-   `NoTimeoutsBeforeGST(s)`: Corresponds to "Suppose no correct node set the timeouts for slots in WINDOWSLOTS(s) before GST".
-   `time >= GST`: Corresponds to the partial synchrony assumption, where liveness is only guaranteed after the Global Stabilization Time (GST).
-   `~>` (leads to): This is the temporal operator for "eventually," representing the "Then..." part of the theorem.
-   `WindowFinalizedState(s)`: Represents the conclusion that "blocks produced by v_l in all slots WINDOWSLOTS(s) will be finalized by all correct nodes."

The assumption "Rotor is successful" is modeled in the TLA+ spec by the `RotorDisseminateSuccess` action, which is weakly fair, ensuring that if a correct leader proposes a block, it will eventually be disseminated to all correct nodes after GST.

## 3. Reasoning and Analysis

The TLA+ code defines a liveness property named `WindowFinalization`. It asserts that under a set of specific, favorable conditions, the system is guaranteed to make progress—specifically, to finalize all blocks within a given leader's window.

Let's break down the logic:

1.  **The Trigger (Antecedent):** The left side of the `~>` operator specifies the conditions that must be met for the liveness guarantee to apply.
    *   `IsFirstSlotOfWindow(s)`: The property applies to an entire window, starting from its first slot `s`. This aligns with the whitepaper's model where leaders are assigned to windows and have special logic for the first slot (e.g., `ParentReady`).
    *   `Leader(s) \in CorrectNodes`: Progress can only be guaranteed if the leader for the window is honest and follows the protocol. A byzantine leader could refuse to produce blocks, stalling the system for its window.
    *   `NoTimeoutsBeforeGST(s)`: This is a crucial premise from Theorem 2. If a correct node has already timed out before the network is stable (before GST), it may have already cast a `SkipVote`. This could prevent the window from being finalized, as the node might not vote for the leader's blocks. This condition ensures we are starting from a "clean slate" at the beginning of the synchronous period.
    *   `time >= GST`: This is the core assumption of the partially synchronous model. Liveness (making progress) is only guaranteed once the network is stable and messages are delivered within a known bound `Delta`.

2.  **The Guarantee (Consequent):** The right side of the `~>` operator is what is eventually expected to happen.
    *   `WindowFinalizedState(s)`: This predicate is defined in `MainProtocol.tla` as:
        ```tla
        WindowFinalizedState(s) ==
            \A v \in CorrectNodes :
                \A i \in (WindowSlots(s) \cap 1..MaxSlot) :
                    \E b \in blocks :
                        /\ b.slot = i
                        /\ b.leader = Leader(s)
                        /\ b \in finalized[v]
        ```
        This correctly formalizes the conclusion of Theorem 2: for every correct validator `v`, and for every slot `i` in the window starting at `s`, there will eventually exist a block `b` in that slot, created by the correct window leader, that is in `v`'s set of finalized blocks.

The overall structure `A ~> B` ("if A is true, then B must eventually become true") is the standard way to express liveness properties in TLA+. The formula accurately captures the essence of Theorem 2 from the whitepaper.

## 4. Conclusion of the Audit

The TLA+ property `WindowFinalization(s)` is a **correct and faithful formalization** of the liveness guarantee described in Theorem 2 of the Alpenglow whitepaper. It correctly identifies the necessary preconditions for progress (correct leader, post-GST, no prior timeouts) and accurately specifies the expected outcome (finalization of all blocks in the window).

The audit finds no discrepancies between the code and the whitepaper's claims for this specific property.

## 5. Open Questions or Concerns

-   The property relies on the weak fairness (`WF_vars`) of several actions (`RotorDisseminateSuccess`, `DeliverVote`, etc.) to ensure the system doesn't get stuck. While this is standard for TLA+ modeling, it's critical that the real-world implementation ensures these actions cannot be starved indefinitely. For example, the networking layer must guarantee eventual message delivery post-GST.
-   The proof of Theorem 2 in the whitepaper is complex and relies on a chain of preceding lemmas. The TLA+ model checker (TLC) is responsible for verifying that `WindowFinalization` holds, which implicitly verifies the logic of those lemmas. Any failure by TLC to prove this property would indicate a flaw in the specification that likely corresponds to a flaw in the reasoning of the whitepaper's proof.

## 6. Suggestions for Improvement

-   The property is well-defined and clear. No improvements are suggested for the TLA+ code itself.
-   For maintainability, it would be beneficial to add a comment directly above the `WindowFinalization` definition explicitly referencing **Theorem 2** in the whitepaper, making the link between the formal spec and the informal document more obvious to future auditors. For example:
    ```tla
    (***************************************************************************
     * THEOREM 2 (Liveness): Under stated premises, every slot in a correct
     * leader's window gets finalized post-GST.
     ***************************************************************************)
    WindowFinalization(s) ==
        (IsFirstSlotOfWindow(s) /\ Leader(s) \in CorrectNodes /\ NoTimeoutsBeforeGST(s) /\ time >= GST) ~>
            WindowFinalizedState(s)
    ```
This concludes the audit for this code block.
