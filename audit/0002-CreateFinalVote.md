# Audit: CreateFinalVote

## 1. Code That Is Being Audited

```tla
CreateFinalVote(validator, slot) ==
    [type |-> "FinalVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]
```

References in repo:
- Messages constructor: `specs/tla/alpenglow/Messages.tla:97`
- Vote validity (FinalVote must have `NoBlock`): `specs/tla/alpenglow/Messages.tla:168`
- Usage in state machine (TRYFINAL): `specs/tla/alpenglow/VotorCore.tla:148`
- Storage multiplicity (only first FinalVote stored): `specs/tla/alpenglow/VoteStorage.tla:76`
- Finalization certificate uses slot-scoped votes (`blockHash = NoBlock`): `specs/tla/alpenglow/Certificates.tla:246`, `specs/tla/alpenglow/Certificates.tla:255`
- `NoBlock` model value mapping: `specs/tla/alpenglow/MC.cfg:41`

## 2. Whitepaper Sections and References

- §2.4 Votes and Certificates — Definition 11 (messages): Table 5 lists “Finalization Vote | FinalVote(s)”. File refs: `alpenglow-whitepaper.md:Page 20` (lines ~495–505 in repo), and `alpenglow-whitepaper.md:478`.
- §2.4 Table 6: “Finalization Cert. | FinalVote | Σ ≥ 60%”. File refs: `alpenglow-whitepaper.md:Page 20` (lines ~505–520).
- §2.5 Definition 12 (storing votes): stores “the first received finalization vote”. File refs: `alpenglow-whitepaper.md:513–520`.
- §2.5 Definition 14 (finalization): slow path finalizes the unique notarized block in slot s; slot-scoped finalization. File refs: `alpenglow-whitepaper.md:536–555`.
- Algorithm 2 TRYFINAL (broadcast FinalVote(s)): `alpenglow-whitepaper.md:702` (line 20 in pseudo-code: “broadcast FinalVote(s)”).

## 3. Reasoning: What the Code Encodes vs. Whitepaper Claims

- Slot-scoped finalization vote:
  - Whitepaper Table 5 defines the Finalization Vote as `FinalVote(s)` (no block hash). Algorithm 2 line 20 also broadcasts `FinalVote(s)`.
  - The code mirrors this by setting `blockHash |-> NoBlock` in `CreateFinalVote`. This models “no block” and signals that finalization votes are tied to the slot, not a particular block.

- Message typing and validity constraints:
  - `Vote` type allows `blockHash ∈ BlockHashes ∪ {NoBlock}`; `IsValidVote` requires `vote.blockHash = NoBlock` for both skip votes and FinalVote. See `specs/tla/alpenglow/Messages.tla:57`, `:168`.
  - Therefore, the constructor is consistent with the typing discipline and validity predicate.

- Single FinalVote per validator/slot (Definition 12):
  - `VoteStorage.CanStoreVote` limits FinalVote to “first received” per validator per slot (no duplicates). See `specs/tla/alpenglow/VoteStorage.tla:76`.
  - This enforces the whitepaper’s multiplicity rule for finalization votes.

- When FinalVote may be issued (TRYFINAL guard matches Algorithm 2 lines 18–21):
  - Guard requires the slot is notarized locally, the validator voted notar for the same block, and the window has not entered fallback (`BadWindow`). See `specs/tla/alpenglow/VotorCore.tla` TRYFINAL.
  - This matches the paper’s slow path condition: only after a notarization certificate and without fallback conflict.

- Finalization certificate structure (Table 6):
  - `CreateFinalizationCert` sets `blockHash |-> NoBlock` and aggregates `FinalVote` for the slot; threshold check uses Σ ≥ 60% (DefaultThreshold). See `specs/tla/alpenglow/Certificates.tla:246–257`.
  - This coheres with slot-scoped FinalVote and Definition 14 (the finalized block is the unique notarized block in slot s).

## 4. Conclusion of the Audit

The `CreateFinalVote` constructor correctly models the whitepaper’s Finalization Vote:
- It is slot-scoped (encodes `FinalVote(s)`), represented by `blockHash = NoBlock`.
- It satisfies message typing and `IsValidVote` constraints.
- It integrates with multiplicity rules (Definition 12) and with certificate creation (Table 6) that expects slot-scoped FinalVote aggregation at the 60% threshold.
- Its use in the state machine (TRYFINAL) matches the whitepaper’s Algorithm 2 conditions for issuing a finalization vote.

No inconsistencies with the whitepaper were found for this constructor.

## 5. Open Questions or Concerns

- Ambiguity risk if multiple notarized blocks exist in a slot: The whitepaper’s Definition 14 assumes a unique notarized block per slot when finalizing via the slow path. This uniqueness is enforced elsewhere (e.g., invariants and Pool certificate rules), not by `CreateFinalVote` itself. Current repo includes invariants for unique notarization; ensure they’re part of the checked model when using this constructor.
- Message shape vs. real-world signatures: The spec models FinalVote without a block hash, consistent with the paper. An implementation may still bind a domain-separated message (e.g., “finalize slot s”) to signatures; the TLA abstraction remains correct.

## 6. Suggestions for Improvement

- Add an explicit helper `IsFinalVote(v) == v.type = "FinalVote"` in `Messages.tla` (parallel to `IsSkipVote`/`IsNotarVote`) for clarity in predicates and queries.
- Consider a comment in `CreateFinalVote` explicitly pointing to Algorithm 2 (TRYFINAL lines 18–21) and Definition 14 to reinforce the slot-scoped rationale.
- Optionally add an invariant tying FinalVote issuance to the `BlockNotarized` state flag (though this is already enforced by `VotorCore.TryFinal`), for additional cross-module clarity in model checking.

Overall, `CreateFinalVote` precisely captures the intended abstraction from the whitepaper with correct integration into typing, storage, and certificate formation.

