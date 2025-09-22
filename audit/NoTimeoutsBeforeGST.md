# Audit Report for NoTimeoutsBeforeGST

## 1. Code Being Audited

```tla
NoTimeoutsBeforeGST(s) ==
    \A v \in CorrectNodes :
        \A i \in (WindowSlots(s) \cap 1..MaxSlot) :
            validators[v].timeouts[i] = 0 \/ validators[v].timeouts[i] >= GST
```

## 2. Whitepaper Section and References

This TLA+ code corresponds to a key premise in the liveness proof of the Alpenglow protocol, specifically **Theorem 2 (liveness)**, located in **Section 2.10** of the `alpenglow-whitepaper.md`.

The theorem is stated as:

> **Theorem 2 (liveness).** Let vℓ be a correct leader of a leader window beginning with slot s. Suppose no correct node set the timeouts for slots in WINDOWSLOTS(s) before GST, and that Rotor is successful for all slots in WINDOWSLOTS(s). Then, blocks produced by vℓ in all slots WINDOWSLOTS(s) will be finalized by all correct nodes.

The predicate `NoTimeoutsBeforeGST(s)` is a direct formalization of the premise: "Suppose no correct node set the timeouts for slots in WINDOWSLOTS(s) before GST".

Other relevant sections include:
- **Section 1.5, "Timeout"**: Explains that timeouts are based on a global protocol parameter Δ.
- **Section 1.5, "Asynchrony"**: Introduces the concept of Global Stabilization Time (GST).
- **Section 2.6, Definition 17 (timeout)**: Defines how timeouts are scheduled.
- **Section 2.10, Lemma 42**: Explains how timeouts are set after GST.

## 3. Reasoning Behind the Code and Whitepaper Claims

The reasoning in the TLA+ code is fully aligned with the claims in the whitepaper.

- **Whitepaper Claim**: The liveness of the protocol (its ability to make progress) is guaranteed only after GST, when the network is synchronous. Before GST, the network is asynchronous, and messages can be arbitrarily delayed. If a correct node's timeout for a slot `i` is set to a value less than GST, it might expire prematurely due to network delays, causing the node to incorrectly vote to skip a slot. This would hinder progress. Therefore, for the liveness proof to hold, it is crucial to assume that for a given leader window, no correct node has set a timeout that would expire before GST.

- **TLA+ Code Logic**: The code formalizes this assumption precisely.
    - `\A v \in CorrectNodes`: It considers all correct (non-Byzantine) nodes.
    - `\A i \in (WindowSlots(s) \cap 1..MaxSlot)`: It iterates through all slots `i` in the leader window that starts at `s`.
    - `validators[v].timeouts[i] = 0 \/ validators[v].timeouts[i] >= GST`: For each slot, it asserts that either the timeout has not been set (is 0) or it is scheduled to occur at or after GST.

This logic correctly captures the whitepaper's assumption that the system is in a state where no timeouts will fire before GST, a necessary precondition for the liveness argument.

## 4. Conclusion of the Audit

The TLA+ code `NoTimeoutsBeforeGST(s)` is a **correct and accurate** formalization of the corresponding premise in the liveness theorem (Theorem 2) of the Alpenglow whitepaper. It correctly models the condition that for the liveness guarantee to hold, the system must be in a state where no timeouts for the relevant window will occur before the Global Stabilization Time (GST).

## 5. Open Questions or Concerns

- The use of `s` as a parameter to `NoTimeoutsBeforeGST` is slightly ambiguous, as `s` is often used to denote the entire state in TLA+. Here, it represents a slot number that determines the window. This is a minor stylistic point and does not affect the correctness of the code.

## 6. Suggestions for Improvement

- To enhance clarity, the parameter `s` in `NoTimeoutsBeforeGST(s)` could be renamed to something more descriptive, such as `startSlot` or `windowStartSlot`. This would make it more explicit that the parameter is a slot number and not the entire state. For example: `NoTimeoutsBeforeGST(startSlot)`. This is a minor suggestion and the current code is not incorrect.
