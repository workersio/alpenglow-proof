# Audit: RotorDisseminateSuccess

1. Code That You Are Auditing

File: `specs/tla/alpenglow/MainProtocol.tla:240`

```tla
RotorDisseminateSuccess(block) ==
    /\ block \in blocks
    /\ block.leader \in CorrectNodes
    /\ LET needers == {v \in Validators : block \notin blockAvailability[v]}
           nextSlot == IF block.slot + 1 <= MaxSlot THEN block.slot + 1 ELSE block.slot
           nextLeader == Leader(nextSlot)
           relays == RotorSelect(block, needers, nextLeader)
       IN /\ needers # {}
          /\ relays # {}
          /\ RotorSuccessful(block.leader, relays, CorrectNodes)
          /\ SliceDelivered([leader |-> block.leader, needers |-> needers], relays, CorrectNodes)
          /\ blockAvailability' = [w \in Validators |-> blockAvailability[w] \union {block}]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>
```

Referenced definitions and variables:

- `Leader(slot)` — VRF leader schedule (Blocks): `specs/tla/alpenglow/Blocks.tla:149`.
- `RotorSelect(block, needers, nextLeader)` — PS-P relay selection (Rotor): `specs/tla/alpenglow/Rotor.tla:210`.
- `RotorSuccessful(leader, relays, correctNodes)` — Definition 6 predicate (Rotor): `specs/tla/alpenglow/Rotor.tla:231`.
- `SliceDelivered(slice, relays, correctNodes)` — 2-hop delivery predicate (Rotor): `specs/tla/alpenglow/Rotor.tla:239`.
- `CorrectNodes == Validators \\ byzantineNodes` — set of correct validators (Main): `specs/tla/alpenglow/MainProtocol.tla:57`.
- `blockAvailability` — Blokstor abstraction (typed and initialized in Main): `specs/tla/alpenglow/MainProtocol.tla:98, 609`.

2. Whitepaper Sections And References Represented

- §2.2 “Rotor” — success condition and dissemination semantics:
  - Definition 6: leader correct and at least γ correct relays: `alpenglow-whitepaper.md:414-416`.
  - Next-leader prioritization (“send to next leader first”): `alpenglow-whitepaper.md:386`.
  - General Rotor overview and pipelining across slices: `alpenglow-whitepaper.md:365-378`.
- §2.3 “Blokstor” — nodes store the first block received through Rotor: `alpenglow-whitepaper.md:460-462`.
- §3.1 “PS-P” — proportional partition sampling used for relay selection (referenced by Rotor): Definition 46 `alpenglow-whitepaper.md:1154-1162` and surrounding discussion.

3. Reasoning: What The Code Does vs What The Whitepaper Claims

- Trigger and guards
  - Requires `block \in blocks` and `block.leader \in CorrectNodes` — models the “correct leader” premise in Definition 6.
  - Computes `needers` as validators that do not yet have the block; `needers # {}` ensures we only disseminate if someone needs it.

- Relay selection and prioritization
  - `nextLeader == Leader(nextSlot)` implements the “send to next leader first” optimization; `RotorSelect` receives `nextLeader` and enforces inclusion when feasible (Rotor’s `NextLeaderConstraint`).
  - `RotorSelect` encapsulates PS-P constraints (Definition 46) and stake/resilience checks; if infeasible, it returns `{}` and this success action won’t fire.

- Success condition (Definition 6)
  - Explicitly requires `RotorSuccessful(block.leader, relays, CorrectNodes)`, i.e., leader is correct and at least `GammaDataShreds = γ` relays are correct.
  - Also asserts `SliceDelivered([leader |-> block.leader, needers |-> needers], relays, CorrectNodes)`, which restates success and additionally checks `relays ⊆ needers` (relays are chosen among nodes that still need the block) — consistent with the two-hop delivery model in §2.2.

- Effect: global availability after success
  - On success, sets `blockAvailability' = [w ∈ Validators |-> blockAvailability[w] ∪ {block}]`, i.e., all validators (including Byzantine) are marked as having the block.
  - Whitepaper: “If the conditions of Definition 6 are met, all correct nodes will receive the block …” (Resilience paragraph after Def. 6). The model strengthens this to “all validators” for simplicity; this is a safe over-approximation for the abstract Blokstor.

- Scheduling and fairness context (from Spec, not in this action body)
  - `WF_vars(∃ b ∈ blocks : RotorDisseminateSuccess(b))` appears in `Fairness` (Main), modeling eventual dissemination under the paper’s partial synchrony assumptions (cf. §2.10), though it is not explicitly gated by GST.

4. Conclusion Of The Audit

- The action is a faithful abstraction of §2.2 Definition 6: when a correct leader selects a relay set containing at least γ correct relays, Rotor succeeds and the block becomes available system-wide. Next-leader prioritization is wired through `RotorSelect` and matches the optimization described in the whitepaper.
- The use of `SliceDelivered` to enforce `relays ⊆ needers` (in addition to `RotorSuccessful`) keeps dissemination consistent with the two-hop model. The effect on `blockAvailability` over-approximates the paper’s “all correct nodes” by granting availability to all validators, which is acceptable at this abstraction and does not harm safety.

5. Open Questions Or Concerns

- Over-approximation of recipients
  - The update sets availability for all validators, not just correct nodes. This is stronger than the text (“all correct nodes will receive”), but benign. If a tighter correspondence is desired, restrict the poststate to `CorrectNodes`.

- Fairness after GST
  - Success fairness is unconditional. The whitepaper’s liveness is assumed after GST (§1.5). Consider gating the fairness annotation by `AfterGST` for fidelity.

- `needers # {}` guard
  - The action forbids a vacuous “success” when no one needs the block. This is reasonable, but the paper does not specify this explicitly. The choice is a harmless modeling convenience.

- Block vs slice granularity
  - Rotor operates per slice; the spec models success at block granularity. This is a standard abstraction but could mask slice-level timing nuances. No safety impact, only liveness/latency modeling granularity.

6. Suggestions For Improvement

- Align recipients with Definition 6 (optional)
  - Update the poststate to only add `block` for `CorrectNodes`:
    - Example: `blockAvailability' = [w ∈ Validators |-> IF w ∈ CorrectNodes THEN blockAvailability[w] ∪ {block} ELSE blockAvailability[w]]`.

- Gate success fairness with GST
  - Change `WF_vars(∃ b : RotorDisseminateSuccess(b))` to be active only when `AfterGST` holds, aligning with partial synchrony.

- Documentation clarity
  - Add a brief comment noting that setting availability for all validators is a deliberate over-approximation of “all correct nodes” in the whitepaper.

- Cross-check selection soundness
  - Keep or strengthen the invariant tying `RotorSelect` to its structural constraints (already present as `RotorSelectSoundness`) so that any non-empty selection used in success is PS-P compliant.

No safety or consistency issues are identified in `RotorDisseminateSuccess`. The action correctly captures the success semantics of Rotor (§2.2, Definition 6), integrates the next-leader optimization, and provides the intended handoff to Blokstor for subsequent voting stages.

