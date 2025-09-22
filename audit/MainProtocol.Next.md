# Audit: MainProtocol.tla Next State Relation

1. Code Under Audit

```
Next ==
    \/ \E v \in Validators, b \in blocks : ReceiveBlock(v, b)
    \/ \E v \in Validators, s \in 1..MaxSlot : ProcessTimeout(v, s)
    \/ \E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s)
    \/ \E v \in Validators, b \in blocks : FinalizeBlock(v, b)
    \/ EmitBlockNotarized
    \/ EmitSafeToNotar
    \/ EmitSafeToSkip
    \/ EmitParentReady
    \/ \E v \in byzantineNodes : ByzantineAction(v)
    \/ \E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p)
    \/ \E l \in Validators, s \in 1..MaxSlot, p \in blocks : ByzantineProposeBlock(l, s, p)
    \/ DeliverVote
    \/ DeliverCertificate
    \/ BroadcastLocalVote
    \/ \E b \in blocks : RotorDisseminateSuccess(b)
    \/ \E b \in blocks : RotorDisseminateFailure(b)
    \/ \E v \in Validators, b \in blocks, s \in Validators : RepairBlock(v, b, s)
    \/ AdvanceTime
```

Reference: `specs/tla/alpenglow/MainProtocol.tla:393`.

2. Whitepaper Sections and References Represented

- Definition 6 (Rotor success): pages 20–22; see also relay selection and dissemination.
- Definitions 12–13 (Pool storage, certificates): page 20–21.
- Definition 14 (Finalization – fast ≥80%, slow ≥60%): page 21.
- Definition 15 (Pool events: BlockNotarized, ParentReady): page 21.
- Definition 16 (Fallback events: SafeToNotar, SafeToSkip): pages 21–22.
- Definition 17 (Timeout scheduling and handling): around page 24 (index shows p. 607 of source file).
- Algorithm 1 (Votor event loop): index p. 634.
- Algorithm 2 (Votor helpers): index p. 676.
- Algorithm 3 (Leader window block creation/optimistic parent): index p. 759.
- Algorithm 4 (Repair): index p. 801.
- Safety (Theorem 1) and Liveness (Theorem 2): page references 247–248; §2.9–2.10.

3. Reasoning and Mapping (Code vs. Whitepaper)

- ReceiveBlock: `ReceiveBlock(v, block)` restricts `v \in CorrectNodes`, `block ∈ blocks`, and requires local availability `block ∈ blockAvailability[v]` before invoking `HandleBlock` (Votor TRYNOTAR). Matches Algorithm 1 “Block” handler and Blokstor event (whitepaper lines 468–470). Ref: `specs/tla/alpenglow/MainProtocol.tla:108`, `specs/tla/alpenglow/VotorCore.tla:211`.

- ProcessTimeout: `ProcessTimeout(v, s)` checks local timer expired and casts skip votes via `HandleTimeout` when `~HasState(...,"Voted")`. Matches Definition 17 and Algorithm 1 line 6. Note AdvanceTime also processes timeouts via `AdvanceClock`. Ref: `specs/tla/alpenglow/MainProtocol.tla:122`, `specs/tla/alpenglow/VotorCore.tla:229`, `specs/tla/alpenglow/VotorCore.tla:320`.

- GenerateCertificateAction: Aggregates votes in pool, forms certs meeting Table 6 thresholds, stores them locally, and enqueues to `messages`. Implements Definition 13. Ref: `specs/tla/alpenglow/MainProtocol.tla:132`, `specs/tla/alpenglow/VoteStorage.tla:181`, `specs/tla/alpenglow/Certificates.tla:1`.

- FinalizeBlock: Fast path if `HasFastFinalizationCert(pool, slot, hash)` or slow path if `HasNotarizationCert ∧ HasFinalizationCert(slot)`. Implements Definition 14. Ref: `specs/tla/alpenglow/MainProtocol.tla:152`, `specs/tla/alpenglow/VoteStorage.tla:231,237`.

- EmitBlockNotarized: Fires when pool holds a notarization cert for b (Definition 15). Ref: `specs/tla/alpenglow/MainProtocol.tla:332`, `specs/tla/alpenglow/VoteStorage.tla:250`.

- EmitParentReady: Requires `IsFirstSlotOfWindow(s)` and `ShouldEmitParentReady(pool, s, parentHash, parentSlot)` which encodes: notarization or notar-fallback of parent and skip certs for gaps (Definition 15). Ref: `specs/tla/alpenglow/MainProtocol.tla:356`, `specs/tla/alpenglow/VoteStorage.tla:261`, `specs/tla/alpenglow/Blocks.tla:149,161`.

- EmitSafeToNotar: Requires already voted but not for b, block locally available, and the fallback inequality: `notar(b) ≥ 40% or (skip(s)+notar(b) ≥ 60% and notar(b) ≥ 20%)`. For non-first slots, also requires parent’s notar-fallback cert; this matches the whitepaper’s retrieval/parent-ready condition. Ref: `specs/tla/alpenglow/MainProtocol.tla:338`, `specs/tla/alpenglow/VoteStorage.tla:276`.

- EmitSafeToSkip: Requires already voted but not skip, and `skip(s) + Σ notar(b) − max notar(b) ≥ 40%`. Ref: `specs/tla/alpenglow/MainProtocol.tla:346`, `specs/tla/alpenglow/VoteStorage.tla:299`.

- HonestProposeBlock / ByzantineProposeBlock: Model leader window creation and potential equivocation/withholding. Honest leaders add block to their availability; Byzantine leaders may target subsets (matching §2.2 examples and Algorithm 3 behavior). Ref: `specs/tla/alpenglow/MainProtocol.tla:164,186`; leader/slot/window helpers in `specs/tla/alpenglow/Blocks.tla:149,161`.

- DeliverVote / BroadcastLocalVote / DeliverCertificate: Dissemination of votes and certs; `BroadcastLocalVote` ensures eventual network push per §2.4 “broadcast to all other nodes”. Ref: `specs/tla/alpenglow/MainProtocol.tla:286,312,298`.

- RotorDisseminateSuccess / Failure: Encodes Definition 6 — success requires leader correct and ≥γ correct relays; success delivers to all; failure delivers only to sampled relays. Uses `RotorSelect`, `RotorSuccessful`, `SliceDelivered`. Ref: `specs/tla/alpenglow/MainProtocol.tla:216,240`, `specs/tla/alpenglow/Rotor.tla:210,231,239`.

- RepairBlock: Algorithm 4 — when pool indicates a notar(ized/fallback) block that we don’t have, fetch from any supplier already storing it. Ref: `specs/tla/alpenglow/MainProtocol.tla:260`.

- AdvanceTime: Partial synchrony model; bumps time and processes timeouts via `AdvanceClock`. Supports §1.5, §2.10 liveness assumptions. Ref: `specs/tla/alpenglow/MainProtocol.tla:202`.

- Fairness Annotations: `Spec == Init /\ [][Next]_vars /\ Fairness` with WF on time progression, network deliveries, pool-driven events, honest proposal, cert generation, rotor success, repair, and per-validator ReceiveBlock after GST. This reflects §2.10 “after GST, honest messages keep flowing.” Ref: `specs/tla/alpenglow/MainProtocol.tla:404`.

- Safety/Liveness Properties: Included invariants and temporal goals match Theorem 1 (single chain) and liveness sketches (eventual finalization), with supporting lemmas (vote uniqueness, unique notarization) aligned to Lemma 20 and related claims. Ref: `specs/tla/alpenglow/MainProtocol.tla:424` onward.

4. Conclusion of the Audit

- The Next relation composes all protocol actions described in the whitepaper and gates each by the corresponding preconditions from Definitions 12–17 and Algorithms 1–4. The mapping is faithful and explicit.
- Vote and certificate thresholds strictly follow Table 6: fast (≥80%), notar/fallback/skip/final (≥60%), with count-once per slot semantics enforced in `Certificates.tla` and `VoteStorage.tla`.
- Fallback events (Definition 16) are encoded exactly, including the non-first-slot parent constraint for SafeToNotar and the “no fast path possible” inequality for SafeToSkip.
- ParentReady (Definition 15) and Repair (Algorithm 4) are correctly integrated into the control flow via `EmitParentReady` and `RepairBlock`.
- Rotor behavior (Definition 6) and dissemination are represented with success/failure variants and structural constraints enforced by `RotorSelect` and `SliceDelivered`.
- Safety invariants (Theorem 1) and support lemmas (vote uniqueness, unique notarization, certificate non-equivocation) are present and consistent with the state machines and storage rules.
- The fairness set captures the intended “messages flow after GST” assumption and is applied to delivery-like actions and pool-emitted events.

Overall, the Next relation and its referenced operators match the whitepaper abstractions and claims. No contradictions with Definitions 12–17, Definition 6, or Theorems 1–2 were found.

5. Open Questions or Concerns

- Dual timeout handling paths: Both `ProcessTimeout` and `AdvanceTime`→`AdvanceClock` can trigger `HandleTimeout`. This seems safe (idempotent via `timeouts[s]=0` and state flags) but is redundant. Consider consolidating to one path to simplify reasoning.

- Fairness coverage for finalization: There is no WF clause for `FinalizeBlock`. Temporal properties (EventualFinalization/Progress) can still hold under existing fairness, but adding `WF_vars(\E v,b : FinalizeBlock(v,b))` could strengthen liveness under adversarial scheduling where finalization remains continuously enabled.

- Naming in Next for `RepairBlock`: The third quantifier uses `s \in Validators` for supplier; reusing `s` (usually a slot variable) may be confusing. Suggest rename to `supplier` for readability (the operator uses that name).

- HonestProposeBlock gating by ParentReady: Honest proposal is allowed whenever `leader = Leader(slot)` and parent is older, regardless of whether `ParentReady` has been emitted. This is consistent with Algorithm 3’s “optimistic” building, and safety is preserved because voting (`TryNotar`) blocks until ParentReady/parent-vote predicates. If stricter modeling is desired, add an optional guard `HasState(validators[leader], slot, "ParentReady")` and/or keep current optimistic semantics as a separate action.

- Cert broadcast criterion in `GenerateCertificateAction`: The candidate selection broadcasts if either the cert is new to `messages` or some validator can still store it. This is a reasonable abstraction of “store then broadcast” but is slightly stronger than the minimal “only when newly added to Pool” phrasing. Not a safety issue; document intent.

- Rotor fairness and feasibility: WF on `RotorDisseminateSuccess` assumes that when the success guard stays enabled (e.g., repeated after new selections), the action eventually occurs. This aligns with §2.2, but if you want to model occasional selection failures under churn, consider an explicit fairness/justice assumption for `RotorSelect` or a probabilistic model (out of scope for TLA+ here).

6. Suggestions for Improvement

- Remove redundancy or comment it: Either drop `ProcessTimeout` from Next or add a brief comment explaining it coexists with `AdvanceClock` for clarity.

- Add optional fairness for finalization: `WF_vars(\E v \in Validators, b \in blocks : FinalizeBlock(v,b))` to strengthen progress under worst-case scheduling during model checking.

- Rename Next’s `RepairBlock` parameter: Change `s \in Validators` to `supplier \in Validators` for readability and to avoid clash with `s` = slot elsewhere.

- Cross-file doc anchors: In code comments, cite precise whitepaper page/section near each action definition (many are already present — great). Add explicit equation snippets for Definition 16 near `CanEmitSafeToNotar/Skip` as was done in comments to ease review.

- Minor precondition tightening (optional): If you prefer stricter leader gating, add `HasState(leader, slot, "ParentReady")` to `HonestProposeBlock`; keep the “optimistic” variant as a separate action for Algorithm 3 semantics.

- Model coverage tests (MC harness): Consider adding temporal checks asserting that ParentReady eventually triggers for first slots of windows under the stated certificate assumptions, and that SafeToNotar/Skip events do not oscillate when thresholds are right at boundaries.

