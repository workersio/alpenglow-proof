**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:419`

```
Fairness ==
    /\ WF_vars(AdvanceTime)
    /\ WF_vars(DeliverVote)
    /\ WF_vars(DeliverCertificate)
    /\ WF_vars(BroadcastLocalVote)
    /\ WF_vars(EmitBlockNotarized)
    /\ WF_vars(EmitSafeToNotar)
    /\ WF_vars(EmitSafeToSkip)
    /\ WF_vars(EmitParentReady)
    /\ WF_vars(\E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p))
    /\ WF_vars(\E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s))
    /\ WF_vars(\E b \in blocks : RotorDisseminateSuccess(b))
    /\ WF_vars(\E v \in Validators, b \in blocks, s \in Validators : RepairBlock(v, b, s))
    /\ \A v \in Validators :
           IF v \in CorrectNodes
           THEN WF_vars(\E b \in blocks : ReceiveBlock(v, b))
           ELSE TRUE
```

Referenced actions and helpers (definitions):
- `AdvanceTime` — `specs/tla/alpenglow/MainProtocol.tla:209`
- `DeliverVote` — `specs/tla/alpenglow/MainProtocol.tla:293`
- `DeliverCertificate` — `specs/tla/alpenglow/MainProtocol.tla:306`
- `BroadcastLocalVote` — `specs/tla/alpenglow/MainProtocol.tla:319`
- `EmitBlockNotarized` — `specs/tla/alpenglow/MainProtocol.tla:337`
- `EmitSafeToNotar` — `specs/tla/alpenglow/MainProtocol.tla:350`
- `EmitSafeToSkip` — `specs/tla/alpenglow/MainProtocol.tla:365`
- `EmitParentReady` — `specs/tla/alpenglow/MainProtocol.tla:381`
- `HonestProposeBlock` — `specs/tla/alpenglow/MainProtocol.tla:120`
- `GenerateCertificateAction` — `specs/tla/alpenglow/MainProtocol.tla:132`
- `RotorDisseminateSuccess` — `specs/tla/alpenglow/MainProtocol.tla:227`
- `RepairBlock` — `specs/tla/alpenglow/MainProtocol.tla:272`
- `ReceiveBlock` — `specs/tla/alpenglow/MainProtocol.tla:98`
- `CorrectNodes` — `specs/tla/alpenglow/MainProtocol.tla:56`


**Whitepaper References**

- Partial synchrony and GST (model and delivery semantics)
  - `alpenglow-whitepaper.md:228`, `alpenglow-whitepaper.md:230`, `alpenglow-whitepaper.md:239`
- Liveness claim and Theorem 2
  - `alpenglow-whitepaper.md:248`, `alpenglow-whitepaper.md:1045`
- Rotor success condition (leader correct and ≥ γ correct relays)
  - `alpenglow-whitepaper.md:414`, `alpenglow-whitepaper.md:416`
- Pool events (Definition 15): BlockNotarized, ParentReady
  - `alpenglow-whitepaper.md:543`
- Fallback events (Definition 16): SafeToNotar, SafeToSkip
  - `alpenglow-whitepaper.md:554`
- Standstill re-transmission to ensure eventual delivery after GST
  - `alpenglow-whitepaper.md:1231`


**Reasoning (Code vs Whitepaper)**

- Fairness intent (weak fairness WF_vars)
  - Models “messages between correct nodes eventually arrive” and “honest actions do not starve” under partial synchrony/GST. Weak fairness requires that an action continuously enabled is eventually taken, aligning with the whitepaper’s eventual delivery and progress premises after GST.

- Network dissemination related fairness
  - `WF_vars(DeliverVote)` and `WF_vars(DeliverCertificate)` ensure that any in-flight vote/certificate will eventually be delivered into all Pools (abstraction used in `DeliverVote`/`DeliverCertificate`). This matches the whitepaper’s eventual delivery model and the standstill retransmission mechanism that guarantees delivery in practice after GST.
    - Vote/cert validity and pool rules are handled in `Messages.tla` / `VoteStorage.tla` (Definition 12, 13), so fairness here preserves consistency.
  - `WF_vars(BroadcastLocalVote)` ensures locally stored honest votes are eventually re-broadcast, matching the “broadcast to all other nodes” narrative in §2.4 and the standstill mechanism.

- Local event generation fairness
  - `WF_vars(EmitBlockNotarized)`, `WF_vars(EmitSafeToNotar)`, `WF_vars(EmitSafeToSkip)`, `WF_vars(EmitParentReady)` enforce that once Pools meet Definition 15/16 conditions, the corresponding events will not be perpetually enabled without firing. This is essential to drive Algorithm 1 progress (Votor) as per pages 24–26 (Algorithms 1–2) and Def. 15/16.

- Leader proposal and certificate assembly fairness
  - `WF_vars(∃ l,s,p : HonestProposeBlock(l,s,p))` captures that if any honest leader/slot/parent triple is continuously enabled, a proposal will eventually be produced (Algorithm 3 context), consistent with §2.7.
  - `WF_vars(∃ v,s : GenerateCertificateAction(v,s))` ensures that when Pools have enough votes (Table 6 thresholds), some validator will eventually aggregate and broadcast the certificate, a prerequisite to drive finalization.

- Rotor and dissemination fairness
  - `WF_vars(∃ b : RotorDisseminateSuccess(b))` aligns with Definition 6: when a correct leader and ≥ γ correct relays are available (structural constraints captured in `Rotor.tla` via `RotorSuccessful` and selection feasibility), successful dissemination is not starved. This reflects the resilience discussion following Def. 6.

- Repair fairness
  - `WF_vars(∃ v,b,s : RepairBlock(v,b,s))` guarantees that if a block needs to be fetched (per §2.8 triggers via notar/notar-fallback), some repair will eventually happen, allowing correct nodes to continue processing and finalize.

- Per-validator receive fairness (correct nodes only)
  - `∀ v ∈ Validators : v ∈ CorrectNodes ⇒ WF_vars(∃ b : ReceiveBlock(v,b))` ensures each correct node will eventually process delivered blocks that remain available, matching the “all correct nodes” quantification in Theorem 2’s conclusion about finalization agreement.

- Scope of fairness vs. GST
  - The comment states the intent is to model the §2.10 liveness premise after GST. The formalization applies WF unconditionally, which is consistent with the paper’s overall assumption that messages between correct nodes are eventually delivered (even before GST, delays can be arbitrary). This is a standard modeling convenience for TLC and is not inconsistent with the text.


**Conclusion**

- The Fairness conjunction correctly encodes the whitepaper’s liveness premises: eventual delivery, eventual local event emission, and non-starvation of key honest actions (proposal, certificate construction, Rotor success, repair, and per-node block processing). These align with Definitions 6, 15, 16 and support Theorem 2.
- The quantification choices are appropriate: per-validator WF for `ReceiveBlock` (to cover all correct nodes), and existential WF for global actions to avoid over-constraining the scheduler while still ensuring progress.
- The fairness set intentionally excludes adversarial actions and non-progress primitives (e.g., Rotor failure), which is correct.


**Open Questions / Concerns**

- Missing fairness for `FinalizeBlock`
  - Without `WF_vars(∃ v,b : FinalizeBlock(v,b))`, TLC could admit behaviors where certificates persist but finalization steps are perpetually starved. This concern is already highlighted in `audit/FinalizeBlock.md` and impacts temporal properties such as `EventualFinalization`.

- GST-gating of fairness
  - The model applies fairness globally; the commentary indicates the post-GST intent. If stricter fidelity to GST is desired, one could gate some fairness with a guard using `AfterGST` or use liveness properties constrained by `(time ≥ GST) ~> ...`. This is a modeling nuance; current form is still consistent with eventual-delivery assumptions and practical retransmission.

- Existential WF vs. per-entity WF
  - For actions like `GenerateCertificateAction` or `RotorDisseminateSuccess`, existential quantification is weaker than per-slot/per-block WF. It suffices for global progress but might allow schedules that systematically starve particular slots/blocks while still making some progress. This is a conscious trade-off; if per-window fairness is required, consider stratified WF by window.

- Delivery fairness covers all messages, not only honest ones
  - `DeliverVote` / `DeliverCertificate` fairness also applies to Byzantine-originated traffic. This is safe for correctness (Pool multiplicity/uniqueness prevent harm) but stronger than the paper’s “messages between correct nodes” phrasing.


**Suggestions for Improvement**

- Add weak fairness for finalization
  - Extend the fairness set with: `WF_vars(\E v \in Validators, b \in blocks : FinalizeBlock(v, b))` to rule out starvation where finalization remains enabled indefinitely.

- Optional: GST-sensitive fairness
  - If desired, gate fairness via guards that only become stable after GST (e.g., `WF_vars(AfterGST /\ DeliverVote)`), or continue using the current specification and keep liveness properties explicitly post-GST (as already done: `(time >= GST) ~> ...`).

- Optional: refine existential WF where stronger guarantees are needed
  - For window-driven progress, consider per-window fairness (e.g., over `IsFirstSlotOfWindow(s)`) to better mirror Theorem 2’s per-window statement while keeping TLC tractable.

- Documentation touch-up
  - Add a short note in `MainProtocol.tla` near `Fairness` clarifying that unconditional WF models eventual delivery/retransmission and scheduler fairness, intended to support §2.10 post-GST liveness proofs.


**Cross-File References**

- Fairness location: `specs/tla/alpenglow/MainProtocol.tla:419`
- Actions referenced (see list above for exact lines): `specs/tla/alpenglow/MainProtocol.tla`
- Event predicates and thresholds: `specs/tla/alpenglow/VoteStorage.tla:214`, `specs/tla/alpenglow/VoteStorage.tla:260`, `specs/tla/alpenglow/VoteStorage.tla:291`
- Rotor success and selection: `specs/tla/alpenglow/Rotor.tla:288`, `specs/tla/alpenglow/Rotor.tla:317`
- Temporal liveness properties: `specs/tla/alpenglow/MainProtocol.tla:540`

