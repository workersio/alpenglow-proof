# Audit: RotorDisseminateFailure

1. Code That You Are Auditing

File: `specs/tla/alpenglow/MainProtocol.tla:258`

```tla
RotorDisseminateFailure(block) ==
    /\ block \in blocks
    /\ LET needers == {v \in Validators : block \notin blockAvailability[v]}
           nextSlot == IF block.slot + 1 <= MaxSlot THEN block.slot + 1 ELSE block.slot
           nextLeader == Leader(nextSlot)
           relays == RotorSelect(block, needers, nextLeader)
       IN /\ needers # {}
          /\ relays # {}
          /\ ~RotorSuccessful(block.leader, relays, CorrectNodes)
          /\ blockAvailability' = [w \in Validators |->
                                        IF w \in relays
                                        THEN blockAvailability[w] \union {block}
                                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>
```

Referenced definitions and variables:

- `Leader(slot)` — VRF leader schedule window-consistent mapping (Blocks): `specs/tla/alpenglow/Blocks.tla:149`.
- `RotorSelect(block, needers, nextLeader)` — PS-P compliant relay selection (Rotor): `specs/tla/alpenglow/Rotor.tla:210`.
- `RotorSuccessful(leader, relays, correctNodes)` — Definition 6 predicate (Rotor): `specs/tla/alpenglow/Rotor.tla:231`.
- `SliceDelivered(slice, relays, correctNodes)` — success-only delivery predicate (not used here) (Rotor): `specs/tla/alpenglow/Rotor.tla:239`.
- `CorrectNodes == Validators \\ byzantineNodes` — correct validator set (Main): `specs/tla/alpenglow/MainProtocol.tla:57`.
- `NeedsBlockRepair(pool, block)` — triggers Repair upon certs (Main helper): `specs/tla/alpenglow/MainProtocol.tla:66`.
- Dissemination/repair context actions in Main: `RepairBlock` (Main): `specs/tla/alpenglow/MainProtocol.tla:278`.
- Rotor constants used indirectly: `GammaDataShreds`, `GammaTotalShreds`, stake constraints (Rotor): `specs/tla/alpenglow/Rotor.tla:23-38`.

2. Whitepaper Sections And References Represented

- §2.2 “Rotor” — Definition 6 (success condition) and “Resilience” paragraph around it: `alpenglow-whitepaper.md:414-418` and context at `alpenglow-whitepaper.md:360-452`.
- Next-leader prioritization optimization (“send to next leader first”): `alpenglow-whitepaper.md:402-420` (pipelined slices and relay priority text within §2.2).
- §2.3 “Blokstor”: storage/availability of blocks disseminated via Rotor: `alpenglow-whitepaper.md:462-472`.
- §2.8 “Repair” — Definition 19 and Algorithm 4 (repair missing blocks): `alpenglow-whitepaper.md:778-828`.

3. Reasoning: What The Code Does vs What The Whitepaper Claims

- Trigger and scope
  - Code: Applies to any `block \in blocks`. Computes `needers` (validators lacking the block), computes `nextLeader` from `nextSlot`, and asks Rotor to select `relays` from `needers`.
  - Paper: Rotor operates per slice but abstractly per block; prioritizes the next leader for lowered latency (§2.2). Modeling at block granularity is a standard abstraction.

- Relay selection
  - Code: `RotorSelect(block, needers, nextLeader)` returns a non-empty relay set subject to PS-P structural constraints, stake coverage, and a hint that includes the next leader if applicable (Rotor module). The selection returns `{}` if infeasible.
  - Paper: §3.1 (referenced from §2.2) specifies stake-fair sampling with over-provisioning. The TLA abstraction enforces: fixed Γ bins, inclusion of large stakeholders, and next-leader preference; this matches intent at the abstraction level.

- Failure condition
  - Code: Requires `needers # {}` and `relays # {}`, and negates success: `~RotorSuccessful(block.leader, relays, CorrectNodes)`. In Rotor, success is “leader is correct ∧ at least γ correct relays” (Definition 6). Thus, failure covers: (i) leader Byzantine, or (ii) leader correct but fewer than γ correct relays.
  - Paper: §2.2 Definition 6 and the “Resilience” paragraph: exactly the complement—if Definition 6 does not hold, Rotor does not guarantee delivery to all correct nodes. The explicit split into two reasons (Byzantine leader vs insufficient correct relays) aligns with the text.

- Effect of failure
  - Code: Only the selected `relays` learn the block: `blockAvailability'` adds `block` for `w ∈ relays`, leaves others unchanged. No global delivery is modeled in the failure branch.
  - Paper: In failure, not all correct nodes necessarily receive the block; however, relays contacted by a correct leader will receive their shreds directly in the first hop (§2.2), matching that only a subset may hold the block.
  - Byzantine leader case: The whitepaper notes a faulty leader may send nothing, “Rotor will immediately fail.” The TLA action allows but does not require a byzantine leader to deliver to some subset: the failure action is optional (no fairness), so the model permits zero dissemination (by not taking this action) or partial dissemination (if the leader chooses to send). This is a reasonable nondeterministic abstraction.

- Next-leader prioritization
  - Code: Computes `nextLeader` via `Leader(nextSlot)` and passes it into `RotorSelect`, which enforces a structural constraint to include the next leader when possible.
  - Paper: “all shred relays send their shred to the next leader first” (§2.2). The model captures this as a selection-side constraint, sufficient at this abstraction.

- Relation to Blokstor and Repair
  - Code: `blockAvailability` abstracts Blokstor (§2.3). After failure, many nodes remain without the block; the `RepairBlock` action (enabled by `NeedsBlockRepair`) supports §2.8 Algorithm 4 when certificates arrive. This matches the whitepaper’s “repair missing earlier block” flow.

- Scheduling and fairness context
  - Code: `Next` includes both RotorDisseminateSuccess and RotorDisseminateFailure; fairness is declared for success but not failure. Thus, under conditions enabling success, dissemination is eventually taken (stronger than the paper unless gated by GST). Failure remains opportunistic.
  - Paper: Liveness after GST; success if Definition 6 holds. The spec’s success fairness is broadly consistent with eventuality intent, though gating by AfterGST would align more precisely with partial synchrony (§1.5).

4. Conclusion Of The Audit

- The action correctly models the complement of Rotor success: when Definition 6 is not satisfied, only the selected relays learn the block and no global delivery occurs. The use of `RotorSelect` with next-leader preference and PS-P constraints aligns with the whitepaper’s relay sampling narrative.
- The treatment of the byzantine leader is acceptable at the abstraction level: the model allows both immediate failure (by not taking the action) and partial dissemination (by taking it), reflecting that a malicious leader can send to none or some subset. Safety is unaffected; recovery is modeled via Repair.
- Interaction with Blokstor (§2.3) and Repair (§2.8) is faithful: partial availability after failure can later be completed after certificates, via `RepairBlock`.

5. Open Questions Or Concerns

- Fairness gating and GST
  - Fairness is applied to success unconditionally (`WF_vars(∃ b : RotorDisseminateSuccess(b))`). The whitepaper’s liveness guarantees apply after GST (§1.5). Consider gating success fairness with `AfterGST` for fidelity.

- Adversary power in failure branch
  - The failure branch uses `RotorSelect` even when the leader is byzantine. A malicious leader could send to an arbitrary subset that does not satisfy PS-P or stake constraints. Restricting to `RotorSelect` may under-approximate adversarial choices; this is fine for safety but may mask liveness corner cases.

- Non-emptiness assumptions
  - The action guards `relays # {}`. The whitepaper allows immediate failure with zero deliveries; the model represents that by allowing inaction rather than an explicit `relays = {}` branch. This is acceptable but could be made explicit for clarity.

- Success/failure partitioning
  - Success requires `block.leader ∈ CorrectNodes`. Failure’s negation captures both insufficient relays and byzantine leader; consider documenting this partition explicitly to aid readers.

6. Suggestions For Improvement

- Split failure into explicit cases
  - Add two actions for clarity without changing behavior:
    - `RotorFailInsufficientRelays(block)`: leader correct ∧ `< γ` correct relays ⇒ only relays learn.
    - `RotorFailByzantineLeader(block)`: leader byzantine ⇒ optionally some subset (any `targets ⊆ Validators`) learn, or none.
  - This removes the implicit restriction that byzantine dissemination must follow `RotorSelect`.

- Gate success fairness after GST
  - Change the fairness annotation to `WF_vars(AfterGST /\\ ∃ b : RotorDisseminateSuccess(b))` or equivalent encoding, aligning with partial synchrony assumptions.

- Optional explicit “no-delivery” failure step
  - Add a no-op failure action (e.g., `RotorNoDissemination(block)`) guarded by leader byzantine, to document the paper’s “immediate fail” case. Behaviorally already permitted, but it improves readability.

- Document interplay with Repair
  - Add a comment in the failure block pointing to `RepairBlock` (§2.8) as the recovery path, to guide readers from partial dissemination to eventual availability.

- Parameterization notes
  - Consider a comment that `nextSlot`’s max-bound branch (`ELSE block.slot`) is a model-boundedness convenience and has no protocol analogue.

No safety issues are identified with RotorDisseminateFailure. The action is a sound abstraction of §2.2’s failure modes and integrates cleanly with Blokstor and Repair. The suggestions target adversary modeling clarity and liveness-fidelity to the whitepaper’s partial synchrony assumptions.

