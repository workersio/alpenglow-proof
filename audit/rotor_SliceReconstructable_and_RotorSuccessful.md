# Audit: Rotor SliceReconstructable and RotorSuccessful

## 1. Code Being Audited

Source: `specs/tla/alpenglow/Rotor.tla:200`, `specs/tla/alpenglow/Rotor.tla:207`

```
SliceReconstructable(receivedShredsCount) ==
    receivedShredsCount >= GammaDataShreds

RotorSuccessful(leader, relays, correctNodes) ==
    /\ leader \in correctNodes
    /\ Cardinality(relays \cap correctNodes) >= GammaDataShreds
```

Related constants and context:
- `specs/tla/alpenglow/Rotor.tla:22`–`:38` — defines `GammaDataShreds` (γ) and assumptions including `3*GammaTotalShreds > 5*GammaDataShreds` (κ > 5/3) and `GammaDataShreds < GammaTotalShreds`.
- `specs/tla/alpenglow/MainProtocol.tla:116` — `CorrectNodes == Validators \\ byzantineNodes`.
- `specs/tla/alpenglow/MainProtocol.tla:122` — `EnoughCorrectRelays(leader, relays) == RotorSuccessful(leader, relays, CorrectNodes)`.
- Relay selection returns a set: `specs/tla/alpenglow/Rotor.tla:186`–`:194` (`RotorSelect` → `PSPSelect` → `BinsToRelaySet`).
- `specs/tla/alpenglow/Rotor.tla:112` — `BinsToRelaySet(bins) == { bins[j] : j \in DOMAIN bins }` (collapses multiplicity).

## 2. Whitepaper Sections and References

- Erasure coding and reconstructability:
  - `alpenglow-whitepaper.md:265` — (Γ,γ) erasure code, any γ pieces reconstruct.
  - `alpenglow-whitepaper.md:267` — Reed–Solomon, κ = Γ/γ.
  - `alpenglow-whitepaper.md:333` — Definition 2 (slice): “Given any γ of the Γ shreds, we can decode”.
  - `alpenglow-whitepaper.md:284` — Decoding requires γ valid pieces for a given Merkle root.
- Rotor success condition:
  - `alpenglow-whitepaper.md:414` — Definition 6: Rotor is successful iff the leader is correct and at least γ of the corresponding relays are correct.
  - `alpenglow-whitepaper.md:418` — Lemma 7 (resilience): κ > 5/3 implies ≥γ correct relays with high probability as γ → ∞.

## 3. Reasoning (Mapping Code ↔ Whitepaper)

- SliceReconstructable
  - What the paper claims: Any γ distinct coding shreds suffice to reconstruct a slice (Reed–Solomon property; Definition 2 and Section 1.6).
  - What the spec expresses: An abstract predicate `receivedShredsCount >= GammaDataShreds`. This captures the threshold nature of reconstructability while explicitly avoiding lower-level mechanics (distinctness, Merkle verification), consistent with the abstraction comment in `Rotor.tla:196`–`:199`.
  - Assessment: Faithful abstraction. It represents the erasure code threshold correctly at the level of TLA+ abstraction (count-only, caller must ensure “distinct, valid shreds”).

- RotorSuccessful
  - What the paper claims (Definition 6): Leader correct AND at least γ of the relays (for this slice) are correct. Lemma 7’s expectation calculation treats “number of correct relays” as out of Γ draws, i.e., counting multiplicity per bin/assignment.
  - What the spec expresses: `leader \in correctNodes` AND `Cardinality(relays ∩ correctNodes) >= GammaDataShreds`, where `relays` is a set derived via `BinsToRelaySet(bins)` (collapsing multiplicity across bins).
  - Key semantic nuance: Whitepaper counts relay assignments (Γ bins) toward γ; the TLA definition counts unique relay nodes after collapsing multiplicity. Example: If one correct validator is assigned to γ bins, it can transmit γ distinct shreds. Whitepaper’s condition would be satisfied (≥γ correct assignments), but the current spec’s `Cardinality(relays ∩ correctNodes)` would be 1 < γ and deem Rotor unsuccessful.
  - Assessment: The current predicate is stricter than the paper (it under-approximates success). It matches the “spirit” only if we interpret “relays” as unique nodes, not assignments; however Lemma 7’s math and the PS-P description (Γ samples) clearly treat multiplicity as meaningful.

## 4. Conclusion of the Audit

- SliceReconstructable: Correct and faithful to the whitepaper’s erasure-coding abstraction. No issues.
- RotorSuccessful: Conceptually aligned with Definition 6, but implemented over a set of unique relays, not the Γ assignments. This can falsely classify some successful scenarios as failures (more conservative than the paper). This conservatism is safe for safety proofs but may harm liveness modeling fidelity (e.g., the model may fail to deliver in cases where the real protocol would deliver because multiplicity supplies ≥γ shreds).

## 5. Open Questions or Concerns

- Multiplicity vs. set collapse: Is it intentional that `RotorSuccessful` ignores bin multiplicity (i.e., counts unique relays instead of correct assignments)? If yes, does the team accept the resulting liveness under-approximation in the model?
- Distinctness and validity of shreds: `SliceReconstructable` assumes the input count reflects distinct, Merkle-validated shreds tied to the same root. Do we want an explicit precondition or commentary to make this assumption visible to downstream users?
- Cross-module consistency: `MainProtocol` uses `RotorSuccessful` to gate dissemination success. If multiplicity is ignored, are we comfortable that certain “successful-in-paper” paths are modeled as failures, affecting liveness properties and model checking outcomes?

## 6. Suggestions for Improvement

- Align success predicate with Γ-assignment multiplicity:
  - Define a bins-aware success predicate:
    - `RotorSuccessfulBins(leader, bins, correctNodes) == /\ leader \in correctNodes /\ Cardinality({ j \in DOMAIN bins : bins[j] \in correctNodes }) >= GammaDataShreds`.
  - Prefer passing `bins` (a function `1..GammaTotalShreds -> Validators`) through the pipeline where Rotor success is checked, or carry both `bins` and `BinsToRelaySet(bins)` so that multiplicity-sensitive checks use `bins`.
  - Update `MainProtocol` to use the bins-aware predicate when determining success vs. repair.
- If keeping the set-based abstraction by design, document it explicitly:
  - Note in `RotorSuccessful`’s comment that it is a conservative approximation that counts unique relays, not assignments; hence it under-approximates success relative to Definition 6.
  - Ensure liveness claims and model-checking expectations are framed accordingly (i.e., proofs/invariants state “under this conservative Rotor model ...”).
- Optional: Connect reconstructability explicitly:
  - Add a helper `CorrectAssignmentsCount(bins, correctNodes)` and a lemma-like comment showing `CorrectAssignmentsCount >= GammaDataShreds => ForAll correct nodes: SliceReconstructable(GammaDataShreds)` under standard delivery assumptions, making the link between Definition 6 and erasure reconstruction explicit in the spec.

