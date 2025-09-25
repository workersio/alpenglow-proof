# Audit: CreateNotarVote

## 1. Code Under Audit

```tla
CreateNotarVote(validator, slot, blockHash) ==
    [type |-> "NotarVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]
```

Implementation location: `specs/tla/alpenglow/Messages.tla:67`.

Related type and helpers in the same file:
- `Vote` record schema: `specs/tla/alpenglow/Messages.tla:53`
- `IsValidVote`: `specs/tla/alpenglow/Messages.tla:163`
- Vote classification helpers (e.g., `IsNotarVote`, `IsInitialVote`): `specs/tla/alpenglow/Messages.tla:112`, `specs/tla/alpenglow/Messages.tla:120`

Known usages:
- Votor casts this vote in `TryNotar`: `specs/tla/alpenglow/VotorCore.tla:122`
- Stake/accounting count this as the initial notarization vote in Pool: e.g., `NotarStake`, `TotalNotarStake`: `specs/tla/alpenglow/VoteStorage.tla:146`, `specs/tla/alpenglow/VoteStorage.tla:162`
- Certificate creation uses only `NotarVote` for fast/notarization certs: `specs/tla/alpenglow/Certificates.tla:116`, `specs/tla/alpenglow/Certificates.tla:122`

## 2. Whitepaper Section and References

Primary mapping (messages and votes):
- Definition 11 (messages): `alpenglow-whitepaper.md:478`
- Table 5 (vote types): `alpenglow-whitepaper.md:489`
  - Row: Notarization Vote — `NotarVote(slot(b), hash(b))`: `alpenglow-whitepaper.md:491`

Threshold context (certificates using NotarVote):
- Table 6 (certificates and thresholds): `alpenglow-whitepaper.md:499`
  - Fast-Finalization Cert. — NotarVote, ≥80%: `alpenglow-whitepaper.md:501`
  - Notarization Cert. — NotarVote, ≥60%: `alpenglow-whitepaper.md:502`

Pool/storage and event context (relevant for initial vote semantics):
- Definition 12 (store at most one initial notarization or skip vote per slot): `alpenglow-whitepaper.md:513`
- Definition 13 (certificates, uniqueness, fast⇒notar⇒fallback implication): `alpenglow-whitepaper.md:520`, `alpenglow-whitepaper.md:534`
- Definition 15 (events inc. BlockNotarized/ParentReady): `alpenglow-whitepaper.md:543`
- Definition 16 (fallback events; `notar(b)` counts notarization votes only): `alpenglow-whitepaper.md:554`, `alpenglow-whitepaper.md:565`

## 3. Reasoning: Code vs. Whitepaper Claims

What the paper specifies:
- Table 5 defines a Notarization Vote as an object of the form `NotarVote(slot(b), hash(b))`, signed by the voting node. It carries exactly the slot and the block hash.
- This is the “initial” approval vote per slot, distinct from fallback votes. It is the only vote type counted in fast-finalization and notarization certificates (Table 6).

What the code implements:
- `CreateNotarVote` constructs a record with fields `type = "NotarVote"`, `validator`, `slot`, `blockHash`. Its shape matches the `Vote` schema in `Messages.tla` and exactly captures `slot(b)` and `hash(b)`.
- Typing/validation: `IsValidVote` ensures that for notarization votes, `blockHash ∈ BlockHashes` and `slot ∈ Slots`. Network ingress (`DeliverVote`) and certificate validation check `IsValidVote` on messages, so the model confines to well-typed votes during protocol operation.
- Usage in Votor: `TryNotar` creates this vote only if the whitepaper’s preconditions hold (Algorithm 2 lines 7–17 mirrored in code): no prior initial vote in slot; parent readiness for first-slot-of-window, or prior-slot notarization of the parent otherwise. After creation, the validator marks `Voted` and `VotedNotar` for that slot and stores the vote in the Pool.
- Pool semantics: `StoreVote` enforces Definition 12 (at most one initial vote per validator per slot). Stake calculations in `VoteStorage.tla` use only `NotarVote` to compute `NotarStake` and `TotalNotarStake`, matching the whitepaper’s use of `notar(b)` in Definition 16 (fallback conditions) as the cumulative stake of notarization votes (not including fallback votes).
- Certificates: `Certificates.tla` uses only `NotarVote` to build Fast-Finalization and Notarization certificates, as per Table 6. This matches the design that the initial vote anchors both the 80% and the 60% first-round thresholds.

Abstraction notes:
- Signatures (σ_v) from Table 5 are intentionally abstracted away. The TLA model reasons in terms of vote sets keyed by `validator` identities and stake weights (`StakeMap`). This is appropriate at the abstraction level for safety/liveness.

Conclusion of reasoning: `CreateNotarVote` captures exactly the whitepaper’s Notarization Vote object and integrates coherently with state machines, storage rules, and certificate thresholds.

## 4. Audit Conclusion

- Conformance: The constructor is correct and complete relative to Definition 11 (Table 5). Field names/types and usage are consistent across modules, and all downstream logic (Pool storage, event triggers, certificate generation, and finalization) treats `NotarVote` per the whitepaper.
- Soundness: No deviations found. The model enforces one initial vote per slot (Def. 12), counts notarization stake from `NotarVote` only where required (Def. 16, Table 6), and uses the vote to trigger the intended protocol progress (Alg. 1–2).

## 5. Open Questions / Concerns

- Constructor preconditions vs. typing: `CreateNotarVote` does not itself assert `slot ∈ Slots` or `blockHash ∈ BlockHashes`; these are enforced by `IsValidVote` and by the callers (e.g., `TryNotar` passes `block.slot` and `block.hash`). This is conventional in TLA+, but a typed wrapper could further reduce misuse.
- Slot–hash consistency: The constructor accepts an arbitrary `(slot, blockHash)` pair. Correct callers (e.g., `TryNotar`) pass consistent values (`slot = block.slot`). An explicit wrapper `CreateNotarVoteForBlock(validator, block)` could encode this consistency by construction.
- Signatures: Table 5 mentions signatures; the model abstracts them away. This is acceptable at this level of abstraction, but the spec could optionally state this abstraction explicitly near the constructors.

## 6. Suggestions for Improvement

- Add a block-typed wrapper to prevent slot–hash pairing mistakes:
  ```tla
  CreateNotarVoteForBlock(v, b) ==
      IF IsValidBlock(b) THEN CreateNotarVote(v, b.slot, b.hash) ELSE CreateNotarVote(v, b.slot, b.hash)
  ```
  (Guarding with `IsValidBlock` clarifies intended use; the else returns the same record but signals intent in proofs.)

- Strengthen a well-formedness invariant for correct-node votes, used in MC:
  - Example invariant: “All locally created votes by correct nodes satisfy `IsValidVote` and use `slot = block.slot`.” This tightens the model without changing behavior.

- Document abstraction of signatures near vote constructors (one sentence): clarify that aggregate signatures are modeled as stake-weighted sets of votes (cf. `StakeFromVotes`), not explicit cryptographic artifacts.

- Optional: add a lemma that `TryNotar`-produced votes are valid by construction, to aid proofs:
  ```tla
  THEOREM TryNotarProducesValidNotarVote ==
      \A v, b : (* guards of TryNotar(v, b) hold *) =>
          IsValidVote(CreateNotarVote(v.id, b.slot, b.hash))
  ```

- Cross-check harness: include a unit MC scenario where a validator equivocates on initial votes (both NotarVote and SkipVote) and show Pool prevents storing the second, reinforcing Lemma 20; current invariants (`MultiplicityRulesRespected`) already cover this but an explicit test run helps operational validation.

---

Overall, `CreateNotarVote` is faithful to the whitepaper’s Definition 11 and integrates cleanly with Pool rules (Def. 12–13), fallback conditions (Def. 16), and certificate thresholds (Table 6). No functional mismatches identified.

