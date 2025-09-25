# Audit: CreateSkipVote

## 1. Code Under Audit

```tla
CreateSkipVote(validator, slot) ==
    [type |-> "SkipVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]
```

Implementation location: `specs/tla/alpenglow/Messages.tla:82`.

Related types and helpers in the same module:
- `Vote` record schema: `specs/tla/alpenglow/Messages.tla:58`
- `VoteType` (includes "SkipVote"): `specs/tla/alpenglow/Messages.tla:35`
- `IsSkipVote`: `specs/tla/alpenglow/Messages.tla:116`
- `IsValidVote` (enforces `blockHash = NoBlock` for skip/final votes): `specs/tla/alpenglow/Messages.tla:163`
- Constants and assumptions (`NoBlock \notin BlockHashes`): `specs/tla/alpenglow/Messages.tla:16`, `specs/tla/alpenglow/Messages.tla:28`

Known usages and downstream logic:
- Votor casts skip votes over unvoted slots in the leader window: `specs/tla/alpenglow/VotorCore.tla:174`
- Pool stake accounting for skip votes: `specs/tla/alpenglow/VoteStorage.tla:156` (SkipStake)
- Skip certificate creation and canonicalization of skip votes: `specs/tla/alpenglow/Certificates.tla:196`, `specs/tla/alpenglow/Certificates.tla:209`

## 2. Whitepaper Section and References

Primary mapping (messages and votes):
- Definition 11 (messages): `alpenglow-whitepaper.md:478`
- Table 5 (vote types): `alpenglow-whitepaper.md:489`
  - Row: Skip Vote — `SkipVote(s)`: `alpenglow-whitepaper.md:493`

Threshold and certificate context (usage of skip votes):
- Table 6 (certificates and thresholds): `alpenglow-whitepaper.md:499`
  - Skip Cert. — SkipVote or SkipFallbackVote, ≥60%: `alpenglow-whitepaper.md:504`

Pool/storage and event context:
- Definition 12 (storing votes; at most one initial notarization or skip vote per validator per slot): `alpenglow-whitepaper.md:513`, `alpenglow-whitepaper.md:515`
- Definition 16 (fallback events; SafeToSkip conditions): `alpenglow-whitepaper.md:554`, `alpenglow-whitepaper.md:571`

## 3. Reasoning: Code vs. Whitepaper Claims

What the paper specifies:
- Table 5 defines a Skip Vote as `SkipVote(s)` for slot `s` (signed by the voter). It carries no block hash because it denotes skipping the slot.
- Skip votes contribute toward the Skip Certificate threshold (≥60%) together with SkipFallback votes (Table 6). They are the “initial” skip votes that are mutually exclusive with initial notarization votes for a validator/slot (Definition 12).
- SafeToSkip (Definition 16) characterizes when nodes may cast skip-fallback votes; it relies on the stake already cast as skip or notarization votes but does not change the shape of the initial skip vote itself.

What the code implements:
- `CreateSkipVote` constructs a well-typed `Vote` record with `type = "SkipVote"`, the caller’s `validator` and `slot`, and `blockHash = NoBlock`. This directly models the fact that skip votes do not reference a block.
- Typing/validation: `IsValidVote` explicitly requires `blockHash = NoBlock` for skip votes (and final votes), and asserts `validator ∈ Validators`, `slot ∈ Slots`. The constant assumption `NoBlock \notin BlockHashes` forbids misinterpreting a real block as a skip sentinel.
- Usage in Votor: `TrySkipWindow` generates skip votes for all slots in the current leader window where the validator has not yet cast an initial vote, matching Algorithm 1/2 narratives for timeouts and fallback-triggered skipping. The state flags `Voted` and `BadWindow` are set consistently and pending blocks for those slots are cleared.
- Pool semantics: `StoreVote` enforces Definition 12’s multiplicity, admitting at most one initial vote (either notarization or skip) per validator per slot. Stake aggregation for skip (`SkipStake`) and Skip Certificate creation (`CanCreateSkipCert`) consider both `SkipVote` and `SkipFallbackVote` as per Table 6. The `CanonicalizeSkipVotes` helper ensures one vote per validator is carried into the certificate, with a preference for `SkipFallbackVote` if both exist for the same validator, reflecting stronger evidence conditions.

Abstraction notes:
- Signatures in Table 5 are abstracted away; votes are modeled as records keyed by `validator` identity and counted via stake weights. This is appropriate for safety/liveness arguments in TLA+.
- Using the `NoBlock` sentinel allows a single `Vote` schema to uniformly represent both block-referencing and blockless votes; `IsValidVote` enforces the intended partition.

Conclusion of reasoning: The constructor exactly captures the whitepaper’s Skip Vote object and integrates correctly with multiplicity rules (Def. 12), fallback logic (Def. 16), and skip certificate thresholds (Table 6).

## 4. Audit Conclusion

- Conformance: Correct and complete relative to Definition 11 (Table 5). The `blockHash = NoBlock` choice matches the paper’s omission of a block reference for skip votes and is enforced by `IsValidVote`.
- Integration: Downstream modules (VotorCore, VoteStorage, Certificates) use `SkipVote` precisely as the whitepaper prescribes: as the unique initial skip decision per validator/slot that contributes toward Skip Certificates and gates fallback behaviors.
- No mismatches found.

## 5. Open Questions / Concerns

- Constructor preconditions: `CreateSkipVote` does not itself assert `validator ∈ Validators` or `slot ∈ Slots`. This is enforced by `IsValidVote` and by callers (e.g., `TrySkipWindow` uses `val.id` and a domain-restricted `s`). This is conventional in TLA+, but worth noting when reasoning about arbitrary environments.
- Event-causality clarity: The paper’s narrative allows casting skip votes after timeouts or when fallback evidence indicates the window is “bad”. The constructor is deliberately pure; the gating logic lives in `VotorCore`. This separation is correct but might benefit from a short comment near the constructor noting it is a format helper, not a policy gate.

## 6. Suggestions for Improvement

- Add a small lemma to document that locally created skip votes are valid by construction:
  ```tla
  THEOREM TrySkipWindowProducesValidSkipVotes ==
      \A v, s \in Slots : (* guards in TrySkipWindow(v, s) ensure ~HasState(v, s, "Voted") *)
          LET vote == CreateSkipVote(v.id, s) IN IsValidVote(vote)
  ```

- Optional typed wrapper to avoid misuse in other contexts:
  ```tla
  CreateSkipVoteForSlot(v, s) == IF s \in Slots THEN CreateSkipVote(v, s) ELSE CreateSkipVote(v, s)
  ```
  (The guard is trivial in this model but documents intent and eases proofs.)

- Cross-reference comment in `Messages.tla` next to the constructor: “Per Table 5, skip votes carry no block hash; `NoBlock` sentinel is enforced by `IsValidVote`.” This aligns the constructor with the whitepaper at the point of definition.

---

Overall, `CreateSkipVote` is faithful to the whitepaper’s Definition 11 and is used consistently with Pool rules (Def. 12), fallback conditions (Def. 16), and certificate thresholds (Table 6). No functional issues identified.

