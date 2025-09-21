# Audit: HonestProposeBlock

1. Code That You Are Auditing

File: `specs/tla/alpenglow/MainProtocol.tla:180`

```tla
HonestProposeBlock(leader, slot, parent) ==
    /\ leader = Leader(slot)
    /\ leader \in CorrectNodes
    /\ parent \in blocks
    /\ slot > parent.slot
    /\ slot <= MaxSlot
    /\ Cardinality(blocks) < MaxBlocks
    /\ LET newBlock == [
           slot |-> slot,
           hash |-> CHOOSE h \in BlockHashes : 
                    h \notin {b.hash : b \in blocks},
           parent |-> parent.hash,
           leader |-> leader
       ]
       IN /\ blocks' = blocks \union {newBlock}
          /\ blockAvailability' = [blockAvailability EXCEPT ![leader] = @ \union {newBlock}]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>
```

2. Whitepaper Sections And References Represented

- §2.7 “Block Creation” (leader builds blocks for a window; parent selection rules; Algorithm 3 “optimistic” building before ParentReady).
- §2.3 “Blokstor” (nodes store/repair blocks; leader has the block locally after proposing).
- §2.2 Rotor is orthogonal here but related to later dissemination; not enforced in this action.
- §2.1 Definitions 3–5 (block structure, hash, and ancestry assumptions).
- §2.5–§2.6 voting logic (TRYNOTAR and ParentReady dependencies) are indirectly relied upon to accept/reject proposed blocks downstream.

3. Reasoning: What The Code Does vs What The Whitepaper Claims

- Leader correctness and schedule
  - Code: `/\ leader = Leader(slot)` with `Leader(slot)` defined in `Blocks.tla` via `LeaderSchedule[slot]`. `LeaderScheduleWindowConsistency` (assumption) keeps leaders constant across a window.
  - Paper: §2.7 “leader window” and VRF-based leader schedule per slot (§1.1/§2.7). Match: Yes.

- Honest leader constraint
  - Code: `/\ leader \in CorrectNodes`. The complementary byzantine case is modeled by `ByzantineProposeBlock`.
  - Paper: §2.2 distinguishes correct vs faulty leaders. Match: Yes.

- Parent selection
  - Code: requires an existing `parent \in blocks` with strictly smaller slot `slot > parent.slot`; no further constraint.
  - Paper: §2.7 requires that for the first slot of a window the leader should (in the common case) build on a parent `b_p` for which ParentReady(s, hash(b_p)) is (or will be) satisfied. Algorithm 3 allows “optimistic” building prior to ParentReady and (only for the first slot) a one-time parent change encoded in the slices.
  - Abstraction gap: The TLA block is an atomic record; slices and one-time parent change are abstracted away. The guard does not explicitly require ParentReady or equivalent; instead, the downstream voting (`TRYNOTAR`) will accept only blocks whose parent choice respects the paper’s rules. Safety is preserved because invalid parents simply fail to gather votes/certificates.

- Slot bounds and model limits
  - Code: `/\ slot <= MaxSlot` and `/\ Cardinality(blocks) < MaxBlocks` bound the state space. Next quantifies `slot \in 1..MaxSlot`.
  - Paper: No direct analogue; these are model-checking bounds. Match: N/A (engineering convenience).

- Block construction and uniqueness of hash
  - Code: `newBlock.hash` is chosen fresh from `BlockHashes` to avoid collisions; fields set as per `Block` type (slot/hash/parent/leader).
  - Paper: §2.1 Definitions 3–4 (block record and hash). Match: Yes, at abstraction level (no payload/slices modeled).

- Local storage for the leader
  - Code: `blockAvailability'` adds `newBlock` for the leader only; others learn the block via Rotor actions.
  - Paper: §2.3 Blokstor and §2.2 Rotor dissemination. Match: Yes (leader immediately stores its own block; dissemination is modeled separately).

- Non-objectives
  - The action does not restrict honest leaders to produce at most one block per slot; this is left to behavior (only honest path exists here) and to downstream acceptance via votes (UniqueNotarization, etc.). The byzantine path explicitly allows equivocation.
  - The action does not enforce “adjacent parent” within the window (e.g., ensure slot s+1 builds on slot s) nor parent readiness. These constraints are enforced by the voting and event machinery; the abstraction tolerates extra, ultimately ignored blocks.

4. Conclusion Of The Audit

- At the block-level abstraction, HonestProposeBlock faithfully captures the essentials of §2.7: a correct, scheduled leader can mint a block for its slot with a unique hash, referencing a prior block, and store it locally. Dissemination and acceptance are handled by other actions.
- The spec intentionally allows more nondeterminism than the concrete protocol (e.g., parent choice without explicit ParentReady, multiple honest proposals per slot). Safety is preserved because invalid parent choices cannot gather notarization/finalization votes, and safety invariants constrain finalized blocks only.
- This design is acceptable if the goal is to keep the propose step minimal and push policy checks into voting. If tighter alignment with §2.7’s “ParentReady” discipline is desired at the propose boundary, minor guard strengthening is recommended (see Suggestions).

5. Open Questions Or Concerns

- ParentReady guard (first-slot discipline)
  - Should HonestProposeBlock encode that when `IsFirstSlotOfWindow(slot)` holds, the chosen `parent` satisfies the ParentReady condition as per Definition 15 (or be known via the certificate preconditions used by `EmitParentReady`)? Right now this is left entirely to the voting layer.

- Honest non-equivocation
  - Should the honest action restrict an honest leader to at most one block per (leader, slot) pair? Today it doesn’t; correctness relies on vote-side uniqueness (Lemma 24) rather than proposal-side restraint.

- Window adjacency
  - §2.7 states that once ParentReady is observed, the leader produces all blocks of its window without delays, chaining each to the previous. Should the spec assert an invariant that any two blocks in consecutive slots by the same correct leader form a parent-child chain unless skip certificates intervene?

- Typing of `slot`
  - The action itself does not state `slot \in Slots`; this is ensured by `Next` quantification and the harness. If this action is ever reused in isolation or by a different harness, adding `slot \in Slots` would strengthen the type discipline.

- Knowledge vs existence
  - The precondition is `parent \in blocks` (global existence). The paper’s flow suggests the leader at least knows the parent’s hash (via certificates) and often has the full block. Do we want to require `parent \in blockAvailability[leader]` (leader knows/stores parent) to model a stricter knowledge discipline, or is hash-only knowledge sufficient for this abstraction?

6. Suggestions For Improvement

- Optional guard: parent readiness at window start
  - Strengthen the guard with a predicate capturing §2.7/Def. 15 discipline:
    - Example: add `IsFirstSlotOfWindow(slot) => CanUseParent(leader, slot, parent)`, where `CanUseParent` checks the same certificate conditions as `ShouldEmitParentReady` (or a simpler abstraction like “leader’s pool can emit ParentReady for (slot, parent)”).

- Honest non-equivocation (semantic constraint)
  - Add an invariant (not a guard) such as: for all correct leaders and all slots, there is at most one block in `blocks` with that `(leader, slot)` pair. This preserves abstraction freedom while documenting the design intent.

- Explicit typing of slot
  - Add `/\ slot \in Slots` to the action for robustness if used outside the `Next` context.

- Explicit validity check (documentation aid)
  - Optionally add a comment or lightweight assertion tying to `IsValidBlock(newBlock)` from `Blocks.tla` to emphasize the intended shape:
    - e.g., `\* newBlock \in Block` or `/\ IsValidBlock(newBlock)` as a postcondition.

- Window-chaining hint (comment or helper)
  - Introduce a helper (purely documentary) like `ExtendsChain(newBlock, blocks)` to signal that new blocks are meant to extend existing chains; keep it non-binding if preserving nondeterminism is desired.

- Knowledge refinement (if desired)
  - Consider tightening to `parent \in blockAvailability[leader]` to encode that the leader “has” the parent locally. This is optional; the current abstraction (hash knowledge suffices) is defensible given how ancestry is modeled.

Overall, no safety bug is identified in this action given the rest of the spec’s voting and certification rules. The suggestions above close the gap between the abstract propose step and §2.7’s ParentReady-centric narrative, if a stricter alignment with the whitepaper text is required.

