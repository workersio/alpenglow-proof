**Code Under Audit**

```
AdvanceTime ==
    /\ time' = time + 1
    /\ validators' = [w \in Validators |->
                        IF w \in CorrectNodes
                        THEN AdvanceClock(validators[w], time')
                        ELSE validators[w]]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, finalized, blockAvailability>>
```

- Reference: `specs/tla/alpenglow/MainProtocol.tla:228`

**Whitepaper References**

- Partial synchrony and GST model: `alpenglow-whitepaper.md:228`, `alpenglow-whitepaper.md:239`
- Definition 17 (timeouts): `alpenglow-whitepaper.md:607` — Timeout(i) scheduled at `clock() + Δ_timeout + (i − s + 1) · Δ_block`
- Lemma 42 (propagation of ParentReady and timeout setting after GST): `alpenglow-whitepaper.md:1041`
- Theorem 2 (liveness after GST, uses timeouts and Rotor success): `alpenglow-whitepaper.md:1045`

**Referenced Spec Items**

- `CorrectNodes == Validators \ byzantineNodes` — `specs/tla/alpenglow/MainProtocol.tla:57`
- `AfterGST == time >= GST` — `specs/tla/alpenglow/MainProtocol.tla:72`
- `AdvanceClock(validator, newTime)` — updates local clock and processes expired timeouts — `specs/tla/alpenglow/VotorCore.tla:303`
- Timeout scheduling at ParentReady: `HandleParentReady` sets `timeouts[s] = clock + Δ_timeout + (s − slot + 1) · Δ_block` — `specs/tla/alpenglow/VotorCore.tla:251`

**Reasoning**

- Intent: Model the passage of global time and trigger honest validators’ timeout handling under partial synchrony (GST model). This is the TLA+ abstraction that ties the whitepaper’s local-clock timeouts (Def. 17) to state transitions.
- Global time tick: `time' = time + 1` provides a discrete clock used for liveness reasoning (e.g., `AfterGST`), aligning with the partial synchrony narrative (whitepaper “Asynchrony/Synchrony” around `:228–239`).
- Honest-local clock advance: For each `w ∈ CorrectNodes`, `AdvanceClock(validators[w], time')` sets `validator.clock := time'` and processes any `timeouts[s]` satisfying `timeouts[s] <= time'`. This matches Definition 17’s semantics: when `ParentReady(s, …)` occurs, `HandleParentReady` schedules `timeouts[i] = clock + Δ_timeout + (i − s + 1)·Δ_block`; subsequently, as `time` advances, `AdvanceClock` fires `HandleTimeout` exactly when `time >= timeout[i]`.
- Byzantine nodes: Non-correct validators are left unchanged here. This is consistent with the model: Byzantine behavior is unconstrained and handled via explicit adversarial actions (e.g., `ByzantineAction`), so we do not rely on their timeouts or local clocks for either safety or liveness arguments.
- Separation of concerns: The action explicitly leaves `blocks, messages, byzantineNodes, finalized, blockAvailability` unchanged, which is correct—mere time progression should not inject messages nor modify block sets; those are modeled by separate actions (delivery, propose, repair, etc.).
- Fairness integration: The spec includes `WF_vars(AdvanceTime)` in `Fairness` (`specs/tla/alpenglow/MainProtocol.tla:418`), ensuring time progresses to enable eventual timeout expiries and, together with Rotor assumptions and GST, to realize liveness per Theorem 2.

**Conclusion**

- The `AdvanceTime` action correctly implements the whitepaper’s partial-synchrony time progression and integrates with the Definition 17 timeout mechanism via `AdvanceClock`. It advances only honest nodes’ local clocks and processes their scheduled timeouts, which is faithful to the abstraction where only correct nodes are required to follow the algorithm. The unchanged variables list is appropriate. The action fits coherently with fairness assumptions and the broader liveness proof structure (Lemmas 41–42, Theorem 2).

**Open Questions / Concerns**

- Dual timeout processing: Both `AdvanceClock` (time-driven) and `ProcessTimeout` (explicit action) can trigger timeout handling. This appears benign (idempotent via clearing `timeouts[slot]` and `Voted` checks) but is redundant. Confirm it’s intentional for model flexibility vs. necessary for some TLC exploration strategy.
- Local vs global time: The model sets each honest validator’s `clock` to the global `time`. This is a standard abstraction, but the paper speaks of local clocks. If future work requires skew modeling, consider whether per-node clock drift needs representation; for the current abstraction, it’s acceptable.
- Byzantine clocks: Byzantine validators’ `clock` never advances here. Since their behavior is adversarial, this is fine; nonetheless, confirm that no other action relies on a Byzantine’s `clock` field (a quick scan shows none do).
- Parameter units: `Δ_timeout`, `Δ_block` are naturals; `time` advances by 1. As an abstraction, all units are discrete ticks. Ensure the model checker configuration (e.g., ranges for `GST`, `Δ_*`) makes timeouts strictly in the future; current constraints (`Δ_block > 0`, `Δ_timeout > 0`) satisfy this.

**Suggestions for Improvement**

- Clarify redundancy: Add a brief comment near `AdvanceTime` or `ProcessTimeout` explaining why both mechanisms exist and asserting idempotence, to avoid confusion for readers.
- Optional simplification: If not required, remove `ProcessTimeout` and rely solely on `AdvanceTime` + `AdvanceClock` for timeout firing; or conversely, drop timeout firing from `AdvanceClock` and keep the explicit `ProcessTimeout` action. Keeping one path reduces state branching.
- Add an invariant: “Timeouts are never scheduled in the past” — e.g., after `HandleParentReady`, assert `\A s ∈ windowSlots : timeouts[s] > validator.clock` to encode the whitepaper note under Definition 17.
- Comment intent: In `AdvanceTime`, note explicitly that only `CorrectNodes` advance clocks by design (Byzantines are unconstrained), tying it to the adversarial model.

