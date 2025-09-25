# Audit: GetVotesForSlot

1. Code That You Are Auditing

```tla
GetVotesForSlot(pool, slot) ==
    UNION {pool.votes[slot][v] : v \in Validators}
```

- Location: `specs/tla/alpenglow/VoteStorage.tla:142`

2. Whitepaper Section And References

- Votes & Certificates overview: §2.4
- Pool and vote storage rules (count-once-per-slot): Definition 12 — `alpenglow-whitepaper.md:513`
- Certificates: Definition 13 — `alpenglow-whitepaper.md:520`
- Fallback events and stake notations notar(b), skip(s): Definition 16 — `alpenglow-whitepaper.md:554` (pages 21–22)
- Tables of vote and certificate types: Table 5 — `alpenglow-whitepaper.md:489`, Table 6 — `alpenglow-whitepaper.md:499`

3. Reasoning: What The Code Does vs. What The Paper Claims

- Intent. The whitepaper defines stake quantities over “votes in Pool.” For a slot `s`, we often need the set of all votes stored locally (by any validator) to compute stake for thresholds and decide certificates/events. `GetVotesForSlot` is the canonical aggregator that produces “all votes in Pool for slot s.”

- Semantics. The expression builds a set of sets `{pool.votes[slot][v] : v ∈ Validators}`—each element is the set of votes Pool has stored for validator `v` in the given `slot`—and takes their set-theoretic UNION, yielding a set of vote records (type Vote). Under the module’s type discipline, this is well-defined and returns a subset of `Vote`.

- Typing/totality. VoteStorage types the pool as `votes: [Slots -> [Validators -> SUBSET Vote]]` (see `specs/tla/alpenglow/VoteStorage.tla:25`, initialized at `:31`). The invariant `PoolTypeOK` asserts `DOMAIN pool.votes = Slots` and `∀ s ∈ Slots : DOMAIN pool.votes[s] = Validators` (see `specs/tla/alpenglow/VoteStorage.tla:322`–`:323`). Messages declares `Validators # {}` (see `specs/tla/alpenglow/Messages.tla:24`). Together, for any `slot ∈ Slots`, each `pool.votes[slot][v]` is defined and is a set (possibly empty), making UNION safe and total.

- Alignment with “count once per slot”. Definition 12 restricts what is stored for each validator and slot (first notarization-or-skip; bounded fallbacks; first final vote). This ensures that stake for initial votes is counted at most once per validator per slot. `GetVotesForSlot` simply aggregates; the “count once” policy is enforced at storage time (via `CanStoreVote` and `StoreVote`) and at stake time (Notar/Skip/Total/Max stake functions deduplicate by validator). This matches Definition 12’s intent.

- Downstream usage honors §2.4/§2.5. The operator feeds:
  - `NotarStake` and `TotalNotarStake` using only NotarVote (initial) per the paper’s “notar(b)” definition (see `specs/tla/alpenglow/VoteStorage.tla:148`, `:163`).
  - `SkipStake` using Skip votes (see `:156`).
  - `MaxNotarStake` (for SafeToSkip formula; see `:170`).
  - `GenerateCertificate`, which uses certificate creation guards consistent with Table 6 and §2.5 (see `:185` and constructors in `specs/tla/alpenglow/Certificates.tla:216`, `:223`, `:230`, `:243`, `:252`).

- Paper mapping. Definition 16 explicitly defines notar(b) and skip(s) as cumulative stake of votes “in Pool” and reminds that stake of any node is counted only once per slot. `GetVotesForSlot` is the precise Pool-side abstraction needed so that those quantities are computed from exactly the locally stored votes.

4. Conclusion

- Correctness. Given the Pool typing and invariants, `GetVotesForSlot` is correct and total. It faithfully represents “all votes for slot s in Pool” and supports the whitepaper’s stake definitions and thresholds. It does not itself perform counting; that is intentionally delegated to storage rules (Def. 12) and to stake-calculation functions that deduplicate validators.

- Whitepaper conformance. The operator matches §2.4–§2.5’s modeling: per-slot, per-validator storage; per-slot aggregation; and downstream use in Def. 16 conditions and certificate creation. There is no mismatch in vote kinds: the stake formulas that require initial notarization votes use only `NotarVote`, while fallback and skip certificates properly allow mixed vote types elsewhere.

5. Open Questions / Concerns

- Domain safety for `slot`. The operator assumes `slot ∈ Slots`. That is true in all current call sites, and making it explicit inside the operator would mask type errors elsewhere. This is a conventional and acceptable TLA+ style, but worth keeping in mind when reusing the operator.

- Dynamic validator sets. The spec models `Validators` as a constant set for the scope of the model run/epoch. If future work models dynamic membership or per-epoch validator sets, hard-coding `Validators` in the union could be subtly incorrect across epoch boundaries unless the pool reshapes its domain accordingly.

- Byzantine multiple initial votes. The multiplicity rule in storage (`CanStoreVote`) ensures only the first notarization-or-skip vote is kept for any `(slot, validator)`. This is key to “count once” correctness. Any relaxing of those storage rules would require revisiting stake calculations and possibly `GetVotesForSlot` call sites.

6. Suggestions for Improvement

- Optional domain-robustness tweak. Replace `Validators` with the function domain to make the operator resilient to any future evolution of pool shape:

  ```tla
  GetVotesForSlot(pool, slot) ==
      UNION { pool.votes[slot][v] : v \in DOMAIN pool.votes[slot] }
  ```

  Under `PoolTypeOK`, this is equivalent but slightly more general and self-justifying.

- Lightweight lemma for clarity. Add (and use as an invariant) a helper lemma to document the type of the result:

  ```tla
  GetVotesForSlotTypeOK(pool, slot) ==
      GetVotesForSlot(pool, slot) \subseteq Vote
  ```

- Comment cross-link. In `VoteStorage.tla`, annotate `GetVotesForSlot` with a short pointer to Def. 16’s notar(b), skip(s) stake definitions, to aid readers in connecting the aggregator to the whitepaper’s formulas.

- Keep “initial-only” stake functions explicit. The current `NotarStake`/`TotalNotarStake` correctly filter `NotarVote` only. Retain that distinction (and avoid broad helpers like “NotarStakeIncludingFallback”) to preserve the exact semantics of Definition 16.

7. External References In Code

- `Validators` (constant, non-empty): `specs/tla/alpenglow/Messages.tla:17`, `specs/tla/alpenglow/Messages.tla:24`
- Pool shape and initialization: `specs/tla/alpenglow/VoteStorage.tla:25`, `specs/tla/alpenglow/VoteStorage.tla:31`
- Pool typing invariant: `specs/tla/alpenglow/VoteStorage.tla:322`, `specs/tla/alpenglow/VoteStorage.tla:323`, `specs/tla/alpenglow/VoteStorage.tla:324`
- Downstream stake functions using `GetVotesForSlot`: `specs/tla/alpenglow/VoteStorage.tla:148`, `specs/tla/alpenglow/VoteStorage.tla:156`, `specs/tla/alpenglow/VoteStorage.tla:163`, `specs/tla/alpenglow/VoteStorage.tla:170`, `specs/tla/alpenglow/VoteStorage.tla:185`

