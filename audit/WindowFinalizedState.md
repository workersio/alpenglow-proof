# Audit Report: `WindowFinalizedState` Predicate

## 1. Code Under Audit

```tla
WindowFinalizedState(s) ==
    \A v \in CorrectNodes :
        \A i \in (WindowSlots(s) \cap 1..MaxSlot) :
            \E b \in blocks :
                /\ b.slot = i
                /\ b.leader = Leader(s)
                /\ b \in finalized[v]
```

## 2. Whitepaper Reference

This predicate corresponds to the liveness guarantee described in **Section 2.10, Theorem 2 (Liveness)**.

**Theorem 2 (liveness):**
> Let v_l be a correct leader of a leader window beginning with slot s. Suppose no correct node set the timeouts for slots in WINDOWSLOTS(s) before GST, and that Rotor is successful for all slots in WINDOWSLOTS(s). Then, blocks produced by v_l in all slots WINDOWSLOTS(s) will be finalized by all correct nodes.

The TLA+ code defines the *outcome* of this theorem—a state in which all blocks from a correct leader's window are, in fact, finalized by all correct nodes.

## 3. Reasoning and Analysis

### Code Interpretation

The `WindowFinalizedState(s)` predicate evaluates to `TRUE` if and only if the following conditions hold:

1.  `\A v \in CorrectNodes`: For every single node `v` that is behaving correctly...
2.  `\A i \in (WindowSlots(s) \cap 1..MaxSlot)`: For every slot `i` within the leader window associated with slot `s`...
3.  `\E b \in blocks`: There must exist a block `b` such that...
    - `b.slot = i`: The block `b` corresponds to the slot `i`.
    - `b.leader = Leader(s)`: The block `b` was proposed by the leader of the window that `s` belongs to. The use of `Leader(s)` implies a single, consistent leader for all slots in that window, which aligns with the whitepaper's definition of a leader window.
    - `b \in finalized[v]`: This block `b` is present in the set of finalized blocks for the correct node `v`.

In summary, the predicate describes a state where every correct node has finalized a complete set of blocks for a specific leader's window, and all those blocks were indeed proposed by that window's designated leader.

### Whitepaper Claims

The whitepaper's **Theorem 2 (Liveness)** asserts that under synchronous network conditions (after GST) and with a correct leader, the protocol *makes progress*. Specifically, it guarantees that all blocks proposed by a correct leader for their entire window will eventually be finalized by all correct nodes.

### Comparison

The TLA+ predicate `WindowFinalizedState(s)` is a precise, formal definition of the state that the liveness theorem claims the system will eventually reach. The overall liveness proof in the TLA+ specification (`MainProtocol.tla`, lines 592-595) uses this predicate to formalize the theorem:

```tla
Liveness ==
    (IsFirstSlotOfWindow(s) /\ Leader(s) \in CorrectNodes /\ NoTimeoutsBeforeGST(s) /\ time >= GST)
    ~> WindowFinalizedState(s)
```

This property reads: "If `s` is the first slot of a window, its leader is correct, no timeouts occurred before GST, and the time is after GST, then eventually the system will reach a state described by `WindowFinalizedState(s)`."

The code correctly and accurately models the successful outcome of the liveness property described in the whitepaper.

## 4. Conclusion

The `WindowFinalizedState(s)` predicate is a **correct** and **accurate** formal representation of the state of successful finalization for a full leader window, as claimed by the liveness guarantee (Theorem 2) in the Alpenglow whitepaper. It serves as the target state for the liveness proof within the TLA+ specification.

## 5. Open Questions or Concerns

- The predicate `WindowFinalizedState(s)` checks that the block's leader is `Leader(s)`. This correctly assumes a single leader for the entire window, which is consistent with the `LeaderScheduleWindowConsistency` assumption in `Blocks.tla`. This is a critical assumption for this predicate to be meaningful and should be highlighted as fundamental to the proof.

## 6. Suggestions for Improvement

- The code is clear and concise. No improvements are suggested.
