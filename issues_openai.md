# Alpenglow TLA+ Specification Audit — Issues and Questions

This file records ambiguities, potential misalignments, and refinement questions discovered while mapping the TLA+ spec in `specs/` to the Alpenglow whitepaper `alpenglow-whitepaper.md`. Each item includes concrete references.

## Directory & Naming

- The instructions referenced a `/spec` directory, but the repository uses `specs/`. No action required, but documenting for consistency.

## Rotor Modeling Additions

1) Extra resilience guards not in the paper
   - In `specs/Rotor.tla`, relay selection feasibility includes `ResilienceOK` and stake thresholds (`RotorMinRelayStake`, `RotorMaxFailedRelayStake`) (specs/Rotor.tla:205–244). These are specification‑level guards beyond the whitepaper’s Def. 6 and Lemmas 7–9 (`alpenglow-whitepaper.md:414`, `:418`, `:431`, `:439`).
   - Impact: This can over‑constrain selection feasibility relative to the paper’s model. It is fine as an environment assumption for model checking, but should be explicitly documented as such when interpreting liveness obligations.
   - Suggestion: Keep the guards, but clarify they are environment/model‑checking constraints, not protocol requirements. Optionally parameterize them to vacuous values in proofs that don’t rely on them.

2) Theorem 2 antecedent lacks explicit Rotor‑success quantification
   - The whitepaper’s Theorem 2 assumes Rotor succeeds for all slots in a window (`alpenglow-whitepaper.md:1045`). The property `WindowFinalization(s)` (specs/MainProtocol.tla:1249–1267) assumes: first slot of window, correct leader, no pre‑GST timeouts, and `time >= GST`. It does not explicitly assert “Rotor succeeds for all i ∈ WINDOWSLOTS(s)”. Rotor success is instead modeled as actions with fairness (specs/MainProtocol.tla:440–520, :746–772).
   - Risk: The liveness property might be stronger than the theorem’s premise or rely on fairness implicitly ensuring success. This is acceptable as a modeling shorthand, but the premise should be stated explicitly to align with the theorem.
   - Suggestion: Amend `WindowFinalization(s)` antecedent or add a helper predicate (e.g., `WindowRotorSuccess(s)`) that assumes rotor success for all slots in `WindowSlots(s)`.

## Certificate Relations

3) Fast ⇒ notar votes subset requirement stronger than paper
   - `FastPathImplication` requires a `NotarizationCert` exists with `notarCert.votes ⊆ fastCert.votes` (specs/Certificates.tla:357–392) and is lifted to pools in `PoolFastPathImplication` (specs/MainProtocol.tla:1008–1020).
   - The paper states the threshold implication (fast ≥80% implies a 60% notarization state) (`alpenglow-whitepaper.md:534`), but it does not require a specific set‑inclusion relation between the two certificate vote sets, especially for network‑learned certificates.
   - Risk: If a node stores a fast certificate and a notar certificate originating from different subsets of NotarVotes (both valid), the subset requirement may fail even though the threshold implication holds.
   - Suggestion: Relax to existence of some notarization cert for the same slot/block (no subset condition), or only enforce subset when both certificates were generated locally from the same vote multiset.

## ParentReady and Window Gating

4) Explicit reliance on `blocks` membership for ParentReady witnesses
   - `ParentReadyImpliesCert` witnesses a `p ∈ blocks` such that `ShouldEmitParentReady` holds (specs/MainProtocol.tla:1285–1305). The paper’s Def. 15 references “previous block b” certified by notar/notar‑fallback and skip certs for gaps (`alpenglow-whitepaper.md:543–:546`). The modeling choice to quantify `p` from `blocks` is reasonable, but it implies the block is already present locally (or in the global `blocks` set).
   - Suggestion: This is consistent with the protocol model, but consider adding a remark that certificates are assumed to be for extant blocks (`CertificateBlockProvenance` enforces this at specs/MainProtocol.tla:1021–1038).

## Bounded‑Time Finalization Modeling

5) δθ recording via `blockAvailability` approximates §1.5
   - `avail80Start`/`avail60Start` are set when `AvailabilityStakeFor(s, h)` crosses threshold (specs/MainProtocol.tla:165–216, :1367–1410; whitepaper §1.5 at `:241`). This abstracts δθ in terms of stake that has reconstructed the block, not directly measured network delays.
   - This is an acceptable modeling choice but is a refinement of the paper’s δθ notion. If used for strict latency bounds, document that the model’s “availability stake” is the surrogate for “nodes within δθ”.

## Genesis Modeling

6) Genesis as slot 0 with self‑parent sentinel
   - `GenesisBlock` is slot 0 with `parent = GenesisHash` (specs/Blocks.tla:54–80). The whitepaper reasons from genesis but does not prescribe representation.
   - Suggestion: Keep (improves ancestry totality). No action.

## Leader Schedule and Byzantine Proposers

7) Byzantine proposer restricted to scheduled leader
   - `ByzantineProposeBlock` still requires `LeaderMatchesSchedule(newBlock)` (specs/MainProtocol.tla:370–418), i.e., faulty leaders only equivocate within scheduled slots. The paper focuses on equivocation/withholding by the scheduled leader (§2.2–§2.3 at `:414`, `:468`), so this is consistent, but note that the spec does not model out‑of‑schedule blocks.
   - Suggestion: Leave as is, since out‑of‑schedule blocks should be ignored; documenting the assumption is sufficient.

## Pool Sequencing Clarification

8) Skip‑fallback implies initial notar vote in same slot for the same node
   - `SkipFallbackAfterInitialNotarAt` (specs/VoteStorage.tla:466–474) encodes a sequencing clarification aligned with Def. 16’s “already voted in s, but not to skip s” (`alpenglow-whitepaper.md:571`). This is a reasonable strengthening but is not explicitly stated in the paper.
   - Suggestion: Keep; it clarifies Algorithm 1 semantics and does not alter protocol behavior.

## Minor/Editorial

9) `FastPathImplication` name vs. whitepaper phrasing
   - The paper’s text around `alpenglow-whitepaper.md:534` reads “fast ⇒ notar ⇒ fallback” at the threshold level. Consider renaming or annotating to stress it’s a storage‑level check, not a logical proof step.

10) Window‑level liveness antecedent
   - `WindowFinalizationAll` quantifies over all slots but relies on fairness for proposal/dissemination (specs/MainProtocol.tla:1255–1267). Consider explicitly including “Leader(s) produces blocks in all `WindowSlots(s)`” if you want the property to be assumption‑complete.

## No Blocking Issues Found

All core safety and liveness claims are captured faithfully. The issues above are either clarifications, explicit modeling premises, or minor strengthenings. The two places where alignment with the whitepaper could be improved are (i) explicitly quantifying Rotor success in the Theorem 2 property and (ii) relaxing the fast⇒notar votes subset requirement to match the whitepaper’s threshold implication.

