# Audit: RotorSelectSound

## 1. Code Under Audit

Source: `specs/tla/alpenglow/Rotor.tla:230`

```tla
RotorSelectSound(block, needers, nextLeader) ==
    LET sel == RotorSelect(block, needers, nextLeader)
    IN 
       /\ (needers # {} /\ ~RotorBinAssignmentPossible(block, needers, nextLeader) => sel = {})
       /\ (sel # {} => 
            \E bins \in [1..GammaTotalShreds -> needers] :
                /\ StructuralBinOK(bins, needers, nextLeader)
                /\ ResilienceOK(BinsToRelaySet(bins))
                /\ BinsToRelaySet(bins) = sel)
```

Referenced identifiers (local module unless noted):
- `RotorSelect` → `specs/tla/alpenglow/Rotor.tla:186`
- `RotorBinAssignmentPossible` → `specs/tla/alpenglow/Rotor.tla:172`
- `StructuralBinOK` → `specs/tla/alpenglow/Rotor.tla:154`
- `ResilienceOK` → `specs/tla/alpenglow/Rotor.tla:162`
- `BinsToRelaySet` → `specs/tla/alpenglow/Rotor.tla:112`

Context where this predicate is enforced:
- `RotorSelectSoundness` invariant quantifies it over all blocks → `specs/tla/alpenglow/MainProtocol.tla:917`
- Included in the main invariant and the TLC model config → `specs/tla/alpenglow/MainProtocol.tla:1059`, `specs/tla/alpenglow/MC.cfg:59`

## 2. Whitepaper Sections and References

- Section 2.2 Rotor (erasure coding and success condition)
  - Definition 6 (Rotor success: correct leader and ≥ γ correct relays): `alpenglow-whitepaper.md:414`
  - Resilience note and “immediate fail” complement: `alpenglow-whitepaper.md:416`
  - Lemma 7 (resilience for κ = Γ/γ > 5/3): `alpenglow-whitepaper.md:418`
  - Operational note: relays send to the next leader first (send-order optimization): `alpenglow-whitepaper.md:386`
- Section 3.1 Smart Sampling
  - Definition 45 (partitioning into k bins): `alpenglow-whitepaper.md:1143`
  - Definition 46 (PS-P steps 1–3: deterministic fills; partition remaining stake; per‑bin sampling): `alpenglow-whitepaper.md:1154`

## 3. Reasoning: Intent vs. Whitepaper

What the predicate states (abstraction):
- Failure implication: if some non-empty `needers` set exists and no structurally/resilience-feasible bin assignment exists (`~RotorBinAssignmentPossible`), then the selection `sel` must be empty. This makes selection “fail closed.”
- Soundness witness: whenever `sel` is non-empty, there exists a full bin assignment `bins : 1..Γ → needers` such that:
  - `StructuralBinOK(bins, needers, nextLeader)` holds (exact Γ bins, PS‑P structural constraints, next leader included if needed, non-empty when dissemination needed)
  - `ResilienceOK(BinsToRelaySet(bins))` holds (stake-based resilience check)
  - The resulting relay set equals the function’s output: `BinsToRelaySet(bins) = sel`.

How this maps to the whitepaper:
- The existence of a per-slice bin assignment of size Γ aligns with Section 2.2’s “Γ shreds” and Section 3.1’s PS‑P (Def. 46). Using a function `bins : 1..Γ → needers` captures multiplicity (large stakeholders may occupy multiple bins) per Def. 46 Step 1.
- `StructuralBinOK` bundles: “exactly Γ bins,” PS‑P structural conditions, and the next-leader prioritization. The next-leader part matches the optimization in `alpenglow-whitepaper.md:386` (send order) but is not a mandated sampling constraint.
- The paper’s success condition (Def. 6) is phrased in terms of “≥ γ correct relays” and κ; it does not introduce a stake-threshold requirement. The predicate’s `ResilienceOK` is thus a spec addition rather than a whitepaper requirement.

## 4. Findings and Conclusion

Overall: The high-level intention is good (non-empty selections must be explainable by a PS‑P‑compliant, Γ‑bin assignment; else selection is empty). However, there are three important mismatches that undermine correctness and/or fidelity to the whitepaper.

- Missing enforcement in RotorSelect (risk: false positives)
  - Issue: `RotorSelect` does not check `RotorBinAssignmentPossible` nor does it verify `StructuralBinOK`/`ResilienceOK`. It simply returns `PSPSelect(needers, nextLeader)` if a stake floor and next‑leader inclusion hold (`specs/tla/alpenglow/Rotor.tla:186-193`).
  - Effect: The first conjunct “if ~RotorBinAssignmentPossible then sel = {}” is not guaranteed by implementation; the second conjunct’s witness may fail to exist even if `sel # {}`. The invariant can be violated by construction.

- PS‑P structural under‑specification (diverges from Definition 46)
  - `PSPConstraint` only requires each “large stakeholder” to appear at least once (≥1 bin), not exactly `⌊ρ_i Γ⌋` bins (Def. 46 Step 1). See `specs/tla/alpenglow/Rotor.tla:136-141`.
  - `TotalDeterministicBins` uses a conservative proxy equal to the count of large stakeholders, not `Σ_i ⌊ρ_i Γ⌋` (`specs/tla/alpenglow/Rotor.tla:60-70`).
  - `PSPBinAssignment` uses `CHOOSE` without stake weighting for remaining bins and even rejects assignments when `Γ > |needers|` (`specs/tla/alpenglow/Rotor.tla:96-108`), though Def. 46 allows multiplicity (same node can fill multiple bins). These choices compromise the soundness witness and fidelity to PS‑P.

- Resilience predicate not from the whitepaper
  - `ResilienceOK(sample) == FailureResilient(sample)` relies on stake‑sum thresholds (`CalculateStake`) and a post‑failure residual condition (`RotorMaxFailedRelayStake`) (`specs/tla/alpenglow/Rotor.tla:121-129,162`). The paper’s resilience for Rotor is expressed via κ and “≥ γ correct relays” (Def. 6; Lemma 7), not via stake sums. As an extra constraint it is fine, but then `RotorSelect` must enforce it before returning a non‑empty set, otherwise the witness clause may be unsatisfied.

Conclusion: As written, `RotorSelectSound` is a desirable property, but it is stronger than what the current `RotorSelect` implementation guarantees and also mixes in a resilience notion (stake‑based) that is orthogonal to the paper’s Rotor success definition (γ distinct correct relays). Without aligning the implementation, this invariant can be false even when the algorithm behaves “reasonably” per the rest of the spec.

## 5. Open Questions / Concerns

- Should `RotorSelect` explicitly refuse to return a non‑empty set when `~RotorBinAssignmentPossible`? If yes, wire the check and return `{}` to satisfy the first conjunct.
- Is the minimum stake requirement (`RotorMinRelayStake`) and residual‑stake resilience (`RotorMaxFailedRelayStake`) intended to be part of Rotor’s spec, or are these model‑checking aids? If the latter, consider moving them to separate invariants rather than embedding them in the witness of `RotorSelectSound`.
- Should `PSPConstraint` encode the exact deterministic multiplicity `Cardinality({j : bins[j] = v}) = ⌊ρ_v Γ⌋` for all “large” v (Def. 46 Step 1), not just “≥ 1”? If not, document why a weaker structural condition is sufficient.
- Why does `PSPBinAssignment` require `GammaTotalShreds <= Cardinality(needers)`? PS‑P allows assigning multiple bins to the same node; the current guard can spuriously rule out feasible assignments.
- The parameter `block` is unused in `BinCandidates`/`RotorBinAssignmentPossible`; is it intended for future constraints (e.g., slice index, per‑block randomness)? If unused, consider dropping to avoid confusion.

## 6. Suggestions for Improvement

- Strengthen `RotorSelect` to match the property
  - Add a feasibility check and enforce structural/resilience constraints:
    - If `needers # {}` and `~RotorBinAssignmentPossible(block, needers, nextLeader)`, return `{}`.
    - Otherwise, compute `bins ∈ BinCandidates(block, needers, nextLeader)` and return `BinsToRelaySet(bins)`; fail closed if no such `bins` exists. This makes the witness in `RotorSelectSound` trivial.

- Tighten PS‑P structural modeling to Definition 46
  - Replace the “≥1 bin per large stakeholder” with exact floors per v: `Cardinality({j : bins[j] = v}) = ⌊ρ_v Γ⌋` for all v with `⌊ρ_v Γ⌋ ≥ 1`.
  - Compute `TotalDeterministicBins(needers) = Σ_{v∈needers} ⌊(StakeMap[v] * Γ)/TotalStake⌋` (bounded by Γ by construction) and assign those bins explicitly (e.g., round‑robin to avoid repeated `CHOOSE`).
  - Remove the `Γ <= |needers|` guard in `PSPBinAssignment`; allow multiplicity so bins can be fully populated even with few needers.
  - For remaining bins, prefer a parameterized partitioning and stake‑proportional sampling stub to better reflect Def. 46 Steps 2–3 (even if abstracted from true randomness).

- Align resilience conditions with the whitepaper or isolate them
  - If you intend to keep stake‑based `ResilienceOK`, then enforce it in `RotorSelect` before returning non‑empty `sel`. Otherwise, revise `RotorSelectSound` to use the paper’s success notion (e.g., state separately that when `sel` is used, success requires `Cardinality(sel ∩ CorrectNodes) ≥ GammaDataShreds`).

- Minor cleanups
  - Clarify or remove the unused `block` parameter in `BinCandidates`/`RotorBinAssignmentPossible` to prevent confusion.
  - Add a comment explaining the “nextLeader inclusion” choice and why it is acceptable to bias sampling vs. the whitepaper’s send‑order optimization.

## 7. Cross-References (for auditors)

- `RotorSelectSound` predicate (this audit): `specs/tla/alpenglow/Rotor.tla:230`
- Implementation returning selections: `specs/tla/alpenglow/Rotor.tla:186`
- Feasibility and candidate bins: `specs/tla/alpenglow/Rotor.tla:166-173`
- PS‑P helpers and constraints: `specs/tla/alpenglow/Rotor.tla:50-141,154-161`
- Stake calculations: `specs/tla/alpenglow/Certificates.tla:64-88`
- Invariant usage: `specs/tla/alpenglow/MainProtocol.tla:917,1059`; model config: `specs/tla/alpenglow/MC.cfg:59`
- Whitepaper anchors: `alpenglow-whitepaper.md:386,414,418,1143,1154`

