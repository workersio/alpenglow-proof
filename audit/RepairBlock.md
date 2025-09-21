**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:278`

```
RepairBlock(v, block, supplier) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ block \notin blockAvailability[v]
    /\ NeedsBlockRepair(validators[v].pool, block)
    /\ supplier \in Validators
    /\ block \in blockAvailability[supplier]
    /\ blockAvailability' = [blockAvailability EXCEPT ![v] = @ \union {block}]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized>>
```

**Whitepaper References**

- Section 2.8 Repair (overview and trigger)
  - `alpenglow-whitepaper.md:778` (heading)
  - “After Pool obtains a certificate of signatures on Notar(slot(b), hash(b)) or NotarFallback(slot(b), hash(b)), the block b … needs to be retrieved.” — `alpenglow-whitepaper.md:780`
- Definition 19 (repair functions), Algorithm 4 (repair procedure)
  - `alpenglow-whitepaper.md:782` (Definition 19)
  - `alpenglow-whitepaper.md:801` (Algorithm 4), with calls to `sampleNode`, `getSliceCount`, `getSliceHash`, `getShred` — `alpenglow-whitepaper.md:806`, `alpenglow-whitepaper.md:809`, `alpenglow-whitepaper.md:812`
- Section 2.3 Blokstor (when blocks must be present locally)
  - “Blokstor can perform the repair procedure … If a block is finalized … Otherwise, before the event SafeToNotar(slot(b), hash(b)) … b has to be stored in the Blokstor as well.” — `alpenglow-whitepaper.md:470`

Related spec context used by this action:

- Repair trigger (certificates)
  - `NeedsBlockRepair(pool, block) == HasNotarizationCert(pool, slot, hash) \/ HasNotarFallbackCert(pool, slot, hash)` — `specs/tla/alpenglow/MainProtocol.tla:66`
  - `HasNotarizationCert` — `specs/tla/alpenglow/VoteStorage.tla:214`
  - `HasNotarFallbackCert` — `specs/tla/alpenglow/VoteStorage.tla:220`
- Availability gating elsewhere (consumes repaired blocks)
  - `ReceiveBlock` requires `block \in blockAvailability[v]` — `specs/tla/alpenglow/MainProtocol.tla:108`
  - `EmitSafeToNotar` requires `b \in blockAvailability[v]` — `specs/tla/alpenglow/MainProtocol.tla:350`
- Availability model and dissemination
  - Type invariant: `blockAvailability \in [Validators -> SUBSET blocks]` — `specs/tla/alpenglow/MainProtocol.tla:609`
  - Rotor success delivers to all validators — `specs/tla/alpenglow/MainProtocol.tla:236`
  - Rotor failure delivers to sampled relays — `specs/tla/alpenglow/MainProtocol.tla:256`
- Fairness (eventual repair)
  - `WF_vars(\E v \in Validators, b \in blocks, s \in Validators : RepairBlock(v, b, s))` — `specs/tla/alpenglow/MainProtocol.tla:431`
- Correct node set
  - `CorrectNodes == Validators \ byzantineNodes` — `specs/tla/alpenglow/MainProtocol.tla:57`

**Reasoning**

- Purpose and abstraction
  - The operator abstracts Algorithm 4 (Section 2.8) by modeling repair as an atomic state transition: if a correct validator v needs block b (as indicated by its Pool holding a notarization or notar‑fallback certificate for b) and any supplier already stores b, then v acquires b by adding it to `blockAvailability[v]`.

- Preconditions match the whitepaper trigger
  - `NeedsBlockRepair` encodes exactly the Section 2.8 trigger: presence of either Notarization or NotarFallback certificate for the targeted block (slot, hash). This is consistent with the text at `alpenglow-whitepaper.md:780` and Definition 19.
  - `block \notin blockAvailability[v]` ensures repair is only performed when the block is currently missing.

- Supplier model
  - The step selects any `supplier \in Validators` such that `block \in blockAvailability[supplier]`. This is a high‑level stand‑in for the iterative, randomized contacts (`sampleNode`) and verification steps in Algorithm 4. It assumes that if any node stores the block, v can eventually obtain it.

- Effects and integration
  - Postcondition updates only `blockAvailability[v]` (monotonic `\union {block}`), leaving all other protocol state unchanged. This aligns with Blokstor semantics: repair affects local availability, not voting state or the global block set.
  - The availability update is necessary to enable `ReceiveBlock` and the fallback event `EmitSafeToNotar`, which both require local presence of the block. This mirrors `alpenglow-whitepaper.md:470`’s requirement that blocks be present in storage prior to emitting relevant events.

- Liveness considerations
  - Fairness includes `RepairBlock`, so when its guard remains continuously enabled (for some `(v, b, supplier)`), the model guarantees eventual repair. This captures the “keep trying sampleNode() until success” behavior of Algorithm 4 under partial synchrony, albeit in a single abstract step.

**Conclusion**

- The operator faithfully abstracts Section 2.8 (Definition 19 and Algorithm 4) at the right level of detail for TLA+. It triggers repair exactly when the Pool indicates it is needed (presence of notarization/notar‑fallback), requires a supplier that already stores the block, and updates only local availability. The integration with `ReceiveBlock` and `EmitSafeToNotar` matches the whitepaper’s expectation that availability precedes downstream events.
- The abstraction is slightly optimistic with respect to adversarial suppliers (see concerns), but consistent with the overall model’s nondeterministic delivery assumptions and weak fairness.

**Open Questions / Concerns**

- Supplier correctness
  - The guard permits `supplier \in Validators` (possibly Byzantine). Algorithm 4 explicitly allows repair calls to fail and retry. As modeled, the step succeeds whenever any supplier has the block, even if only Byzantine nodes do. This is an optimistic abstraction; in scenarios where all holders are Byzantine and uncooperative, the model still allows success.

- Fairness gating vs. GST
  - Unlike other dissemination steps, fairness for repair is not gated by `AfterGST`. Section 2.10’s “after GST honest messages keep flowing” could justify gating repair fairness similarly for consistency.

- Trigger completeness across certificate types
  - `NeedsBlockRepair` looks for notarization/notar‑fallback. Per the current `GenerateCertificate`, fast‑finalization also co‑produces notarization/notar‑fallback, so the trigger remains adequate. If that coupling changes, including `HasFastFinalizationCert` in the trigger would preserve correctness.

- Existence of the block object
  - Certificates refer to `blockHash`, not a `block` object. The operator requires `block \in blocks`, so it cannot repair for a certified hash unless the corresponding `block` record exists. This is consistent elsewhere (e.g., events use `b \in blocks`), but it implies the model ignores repair of “unknown” block objects even if a certificate exists for their hashes.

**Suggestions for Improvement**

- Require honest supplier (optional but tighter)
  - Strengthen the guard to `supplier \in CorrectNodes`. This reduces reliance on optimistic nondeterminism and better matches the retry‑until‑success intuition of Algorithm 4, since at least one correct holder must exist in notarization scenarios.

- Consider gating repair fairness after GST
  - Add `AfterGST` to the fairness condition or as a guard to reflect partial synchrony assumptions: e.g., `WF_vars(AfterGST /\ \E v,b,s : RepairBlock(v,b,s))`.

- Make trigger robust to fast‑only implementations
  - Future‑proof `NeedsBlockRepair` by including fast‑finalization: `HasFastFinalizationCert(pool, slot, hash) \/ ...`. This is a no‑op today given `GenerateCertificate` also stores Notarization when Fast is possible, but it documents the intent explicitly.

- Optional: link repair to Blokstor language
  - If you later model Blokstor explicitly, alias `blockAvailability` to its storage predicate or update both to preserve a single source of truth.

**Cross-File References (for this block)**

- Main action under audit: `specs/tla/alpenglow/MainProtocol.tla:278`
- Repair trigger: `specs/tla/alpenglow/MainProtocol.tla:66`
- Certificate queries: `specs/tla/alpenglow/VoteStorage.tla:214`, `specs/tla/alpenglow/VoteStorage.tla:220`
- Availability consumers: `specs/tla/alpenglow/MainProtocol.tla:108`, `specs/tla/alpenglow/MainProtocol.tla:350`
- Rotor delivery semantics: `specs/tla/alpenglow/MainProtocol.tla:236`, `specs/tla/alpenglow/MainProtocol.tla:256`
- Type invariant: `specs/tla/alpenglow/MainProtocol.tla:609`
- Fairness clause: `specs/tla/alpenglow/MainProtocol.tla:431`

