# Audit: ConflictingVotes (Messages.tla)

1. Code that you are auditing.

```
ConflictingVotes(vote1, vote2) ==
    /\ vote1.validator = vote2.validator  \* Same validator
    /\ vote1.slot = vote2.slot            \* Same slot
    /\ IsInitialVote(vote1)               \* Both are initial votes
    /\ IsInitialVote(vote2)
    /\ vote1.type # vote2.type            \* But different types!
```

- Source: `specs/tla/alpenglow/Messages.tla:172`
- Dependency referenced: `IsInitialVote` defined at `specs/tla/alpenglow/Messages.tla:120`

2. The whitepaper section and references that the code represents.

- Definition 11 (messages): `alpenglow-whitepaper.md:478`
- Definition 12 (storing votes): `alpenglow-whitepaper.md:513`
  - “The first received notarization or skip vote …” (per slot, per node)
- Lemma 20 (notarization or skip): `alpenglow-whitepaper.md:820`
  - “A correct node exclusively casts only one notarization vote or skip vote per slot.”
- Context in spec that consumes this abstraction:
  - VoteUniqueness lemma uses `IsInitialVote` to enforce at most one initial vote per slot: `specs/tla/alpenglow/MainProtocol.tla:788`, `specs/tla/alpenglow/MainProtocol.tla:793`
  - Model config includes `VoteUniqueness` as an invariant: `specs/tla/alpenglow/MC.cfg:54`

3. The reasoning behind the code and what the whitepaper claims.

- Whitepaper intent (abstraction): For each slot and validator, there is at most one initial vote, where “initial vote” ∈ {NotarVote, SkipVote}. This is made explicit by Definition 12 (Pool stores only the first notarization or skip vote) and Lemma 20 (a correct node casts only one such vote per slot).
- TLA helper `IsInitialVote` aligns with that abstraction by classifying initial votes exactly as {"NotarVote", "SkipVote"} (`specs/tla/alpenglow/Messages.tla:120`).
- The purpose of `ConflictingVotes` as commented in code is to “help verify Lemma 20 — validators vote once per slot” (`specs/tla/alpenglow/Messages.tla:170`). To correctly reflect Lemma 20, any two initial votes by the same validator for the same slot should be in conflict (regardless of whether both are NotarVote, both are SkipVote, or one of each).
- Current predicate only flags cross-type initial votes (`vote1.type # vote2.type`). It fails to flag same-type equivocation, e.g.:
  - Two NotarVote with different `blockHash` in the same slot by the same validator (forbidden by Lemma 20 and by Definition 12’s “first received [initial] vote”).
  - Two SkipVote in the same slot by the same validator.
- In the broader spec, Lemma 20 is enforced via a set cardinality check (`VoteUniqueness`, `specs/tla/alpenglow/MainProtocol.tla:788`–`specs/tla/alpenglow/MainProtocol.tla:795`), so the overall model captures the whitepaper’s property. However, the local `ConflictingVotes` helper, as written, does not independently characterize “double initial voting” and is currently unused elsewhere (`rg` shows no references beyond its definition).

4. The conclusion of the audit.

- Alignment: `IsInitialVote` matches the whitepaper’s notion of “initial vote”.
- Gap: `ConflictingVotes` incompletely represents the whitepaper’s Lemma 20; it only detects cross-type initial vote conflicts and misses same-type initial vote conflicts. As a result, if this predicate were used to assert non-equivocation, it would not be sufficient to prove the lemma.
- Mitigating context: The model uses `VoteUniqueness` (cardinality-based) to check Lemma 20, so current proofs do not rely on `ConflictingVotes`. Still, the helper is misleading given its name and comment.

5. Any open questions or concerns.

- Intent question: Was `ConflictingVotes` intended to capture any pair of distinct initial votes (regardless of type), or only cross-type equivocation? The comment suggests the former (Lemma 20), but the code implements the latter.
- Data structure semantics: Are votes stored as sets of records (deduplicating identical records)? If so, “two identical SkipVote” duplicates would not co-exist in a set, but two NotarVote for different `blockHash` would, and should be deemed conflicting per Lemma 20.
- Scope: Should `ConflictingVotes` be used in invariants to complement `VoteUniqueness`, or is it purely a local helper? If retained, consistency with Lemma 20 would be desirable to avoid confusion.

6. Any suggestions for improvement.

- Predicate fix (most faithful to Lemma 20): Treat any two distinct initial votes by the same validator for the same slot as conflicting, regardless of type or block hash.

  Suggested TLA refinement:

  ```
  ConflictingVotes(v1, v2) ==
      /\ v1.validator = v2.validator
      /\ v1.slot = v2.slot
      /\ IsInitialVote(v1)
      /\ IsInitialVote(v2)
      /\ v1 # v2
  ```

  Rationale: In a set-based model, `v1 # v2` implies the two records differ in at least one field (type and/or blockHash), which aligns with “more than one initial vote” forbidden by Lemma 20 and Definition 12.

- Alternative stricter variant (if you prefer to be explicit about notarization conflicts by block hash):

  ```
  ConflictingVotes(v1, v2) ==
      /\ v1.validator = v2.validator
      /\ v1.slot = v2.slot
      /\ IsInitialVote(v1)
      /\ IsInitialVote(v2)
      /\ (v1.type # v2.type)
          \/ (v1.type = "NotarVote" /\ v2.type = "NotarVote" /\ v1.blockHash # v2.blockHash)
          \/ (v1.type = "SkipVote" /\ v2.type = "SkipVote")
  ```

  This explicitly enumerates the same-type cases; functionally equivalent to the simpler `v1 # v2` when using set semantics.

- Consistency: Update the comment above `ConflictingVotes` to reference Lemma 20 and Definition 12 precisely, and clarify that the predicate captures any double initial voting, not only cross-type.

- Usage: If the intent is to leverage this helper, consider adding an invariant formulated via `ConflictingVotes` over each validator’s per-slot pool, or rely solely on `VoteUniqueness` to avoid redundancy. Example invariant sketch:

  ```
  NoDoubleInitialVotes ==
      \A v \in Validators : \A s \in Slots :
          ~\E v1, v2 \in validators[v].poolBySlot[s] : ConflictingVotes(v1, v2)
  ```

  Note: adjust `poolBySlot` to your actual state variable naming; currently `VoteUniqueness` already proves the desired bound using `IsInitialVote`.

- Hygiene: If `ConflictingVotes` remains unused and a potential source of confusion, consider either removing it or renaming it to `CrossTypeInitialConflict` with a clarifying comment.

