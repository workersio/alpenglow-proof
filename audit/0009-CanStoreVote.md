# Audit: CanStoreVote (Vote multiplicity rules)

1. Code that you are auditing

```tla
CanStoreVote(pool, vote) ==
    LET 
        slot == vote.slot
        validator == vote.validator
        existingVotes == pool.votes[slot][validator]
    IN
        CASE vote.type = "NotarVote" ->
            \* Can only store if no initial vote (Notar or Skip) exists yet
            ~\E v \in existingVotes : v.type \in {"NotarVote", "SkipVote"}

        [] vote.type = "SkipVote" ->
            \* Can only store if no initial vote (Notar or Skip) exists yet
            ~\E v \in existingVotes : v.type \in {"NotarVote", "SkipVote"}
            
        [] vote.type = "NotarFallbackVote" ->
            \* Can store up to 3 notar-fallback votes
            Cardinality({v \in existingVotes : v.type = "NotarFallbackVote"}) < 3
            
        [] vote.type = "SkipFallbackVote" ->
            \* Can only store if no SkipFallbackVote exists yet
            ~\E v \in existingVotes : v.type = "SkipFallbackVote"
            
        [] vote.type = "FinalVote" ->
            \* Can only store if no FinalVote exists yet
            ~\E v \in existingVotes : v.type = "FinalVote"
            
        [] OTHER -> FALSE
```

Source: `specs/tla/alpenglow/VoteStorage.tla:54`

2. The whitepaper section and references that the code represents

- Definition 12 (storing votes) — Pool multiplicity rules: `alpenglow-whitepaper.md:513` (p.20–21)
  - “The first received notarization or skip vote,”
  - “up to 3 received notar-fallback votes,”
  - “the first received skip-fallback vote,”
  - “the first received finalization vote.”
- Related: Lemma 20 (one initial vote per slot by a correct node): `alpenglow-whitepaper.md:822`
- Operational context: votes/certificates families (Tables 5–6): `alpenglow-whitepaper.md:478`–`:522`

3. Reasoning behind the code and what the whitepaper claims

- Scope and abstraction
  - This predicate governs per-validator, per-slot acceptance caps for stored votes in the validator’s Pool (abstraction only; not network or cryptographic details).
  - It is used by `StoreVote` to admit or reject a received vote without mutating the Pool when caps are violated.

- Mapping to Definition 12
  - Initial vote uniqueness (first notarization or skip): both branches for `"NotarVote"` and `"SkipVote"` check that no initial vote is already present in `existingVotes`. This enforces the “first received notarization or skip vote” rule per validator per slot.
  - Bounded notar-fallbacks: the `"NotarFallbackVote"` branch uses `Cardinality(…)=< 2` before insert (expressed as `< 3` on the pre-state), which admits the first three such votes and rejects further ones, matching “up to 3 received notar-fallback votes.”
  - Single skip-fallback and finalization: the `"SkipFallbackVote"` and `"FinalVote"` branches require absence of an existing same-type vote, matching “the first received …” clauses.
  - Catch-all: `OTHER -> FALSE` rejects any non-specified vote type, keeping the Pool aligned with the message family of Table 5.

- Interactions and system-level coherence
  - Count-once-per-slot: Although fallback votes may coexist with an initial vote for the same validator/slot, certificate stake functions deduplicate by validator (`Certificates.UniqueValidators`/`StakeFromVotes`), satisfying Definition 12’s “count once” requirement when forming certificates.
  - Creation vs storage duties: Correct nodes only create fallback votes under Definition 16 (SafeToNotar/SafeToSkip) once they have already cast an initial vote. Storage does not (and should not) re-check those behavioral preconditions — it solely enforces multiplicity caps. The event gating is specified in `VotorCore.tla`.
  - Validation on ingress: The top-level `DeliverVote` action stores only votes that satisfy `IsValidVote` (see `specs/tla/alpenglow/MainProtocol.tla:547`), so Pool contents remain well-typed.
  - Invariants: The spec exposes `MultiplicityRulesRespected(pool)` and asserts it over all validators (`MainProtocol.tla:896`), so TLC can check that all state transitions preserve the multiplicity guarantees implemented here.

4. Conclusion of the audit

- The predicate precisely encodes Definition 12’s multiplicity constraints for Pool storage:
  - At most one initial vote (NotarVote or SkipVote) per validator per slot.
  - Up to three NotarFallbackVote per validator per slot.
  - At most one SkipFallbackVote and one FinalVote per validator per slot.
- It composes correctly with the rest of the spec:
  - Vote creation guards in `VotorCore` implement the behavioral preconditions (Definitions 15–16) and Lemma 22 non-overlap between finalization and fallback votes.
  - Certificate creation/validation in `Certificates` respects “count once” semantics and threshold checks, independent of multiplicity caps.
  - Global invariants in `MainProtocol` assert Pool multiplicity and certificate uniqueness properties, aligning with Definitions 12–13.
- Net: The implementation matches the whitepaper’s abstraction accurately and is safe under the modeled assumptions.

5. Open questions or concerns

- Byzantine-only fallback votes: The Pool admits fallback votes even if an initial vote from that validator is absent. This matches Definition 12 (which speaks only about storage multiplicity) and is acceptable because creation preconditions are enforced for correct nodes elsewhere. If desired, an optional commentary could clarify this subtlety to prevent misinterpretation.
- Exact fallback cap “3”: The cap matches the whitepaper. If the paper or parameterization evolves, consider exposing this as a named constant (e.g., `MaxNotarFallbacks == 3`) to avoid magic numbers.

6. Suggestions for improvement

- Readability: Replace duplicated initial-vote checks with `Messages.IsInitialVote(v)` to express intent directly:
  - `~\E v \in existingVotes : IsInitialVote(v)`
- Parameterize caps: Introduce constants for per-type caps:
  - `MaxNotarFallbacks == 3`, `MaxSkipFallbacks == 1`, `MaxFinalVotes == 1` and use them in guards and invariants.
- Strengthen documentation links: Add a brief comment referencing `MainProtocol.DeliverVote`’s `IsValidVote` check near `StoreVote` to make the end-to-end validity path obvious to readers.
- Optional invariant: Add a lemma tying `StoreVote` to `MultiplicityRulesRespected` (post-condition) to make the proof obligation explicit for TLC when stepping through `DeliverVote`.

