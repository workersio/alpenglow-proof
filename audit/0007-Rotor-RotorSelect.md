# Audit: RotorSelect

## 1. Code Under Audit

TLA+ snippet (source in `specs/tla/alpenglow/Rotor.tla:47`):

```tla
RotorSelect(block, needers, nextLeader) ==
    IF needers = {} THEN {}
    ELSE LET psSelection == PSPSelect(needers, nextLeader)
         IN IF /\ psSelection \subseteq needers
               /\ CalculateStake(psSelection) >= RotorMinRelayStake
               /\ (nextLeader \in needers => nextLeader \in psSelection)
            THEN psSelection
            ELSE {} \* Explicit failure - insufficient needers/stake
```

Referenced identifiers and definitions:

- `PSPSelect(needers, nextLeader)` → `specs/tla/alpenglow/Rotor.tla:116` (bin-based PS‑P selection via `PSPBinAssignment` and `BinsToRelaySet`).
- `CalculateStake(S)` and `TotalStake` → `specs/tla/alpenglow/Certificates.tla:75` and `:64`.
- `RotorMinRelayStake`, `RotorMaxFailedRelayStake`, `GammaTotalShreds`, `GammaDataShreds` assumptions → `specs/tla/alpenglow/Rotor.tla:22-38`; model values in `specs/tla/alpenglow/MC.cfg:30-36`.
- `RotorSelectSound(block, needers, nextLeader)` witness property tying selections to structural bin assignments and resilience → `specs/tla/alpenglow/Rotor.tla:91`.
- Top-level invariant that applies `RotorSelectSound` across blocks → `specs/tla/alpenglow/MainProtocol.tla:38` (`RotorSelectSoundness`).
- Supporting bin/PS‑P helpers: `PSPBinAssignment`, `PSPConstraint`, `LargeStakeholders`, `DeterministicBinCount`, `BinsToRelaySet`, `ResilienceOK` → `specs/tla/alpenglow/Rotor.tla:50-140, 154-173`.

## 2. Whitepaper Sections and References

- Rotor success and erasure coding basics (Section 2.2):
  - Definition 6 (success condition: correct leader and at least γ correct relays): `alpenglow-whitepaper.md:55-59` (page 17 marker).
  - Reed–Solomon parameters and κ > 5/3 resilience premise (Lemma 7): `alpenglow-whitepaper.md:59-61`.
- Rotor operational description (Section 2.2):
  - Per-slice Γ shreds; leader selects relays; relays forward to nodes that “still need it”; next leader is prioritized in send order (not selection): `alpenglow-whitepaper.md:19-29`.
- Smart Sampling PS‑P (Section 3.1):
  - Definition 45 (partitioning of stakes into bins): `alpenglow-whitepaper.md:16-25` (page 40 marker).
  - Definition 46 (PS‑P steps 1–3): deterministic bin fills for large stakeholders; partition remaining stake into remaining bins; sample one node per bin proportionally to stake: `alpenglow-whitepaper.md:27-33` (page 40 marker).

## 3. Reasoning: What the Code Does vs. Whitepaper Claims

- Purpose and abstraction
  - `RotorSelect` returns a set of relays for a slice (parameter `block` is unused in the function itself). It uses a bin-based helper `PSPSelect` and enforces: domain restriction (`⊆ needers`), minimum stake threshold (`CalculateStake ≥ RotorMinRelayStake`), and mandatory inclusion of `nextLeader` if it still needs the block.
  - The whitepaper requires that for each slice we (a) create Γ shreds, (b) pick Γ relay samples using PS‑P (Definition 46), and (c) Rotor succeeds if ≥ γ correct relays participate (Definition 6).

- PS‑P fidelity
  - The spec models PS‑P with bins (`PSPBinAssignment`) and then collapses bins to a set of unique relays (`BinsToRelaySet`). This is a reasonable abstraction for downstream invariants that care about “which relays” rather than multiplicity.
  - However, the modeling of PS‑P Step 1 is weakened: the code recognizes “large stakeholders” as those with `⌊ρ_i Γ⌋ ≥ 1` but only requires “≥1 bin” per such node (`PSPConstraint`), not the exact `⌊ρ_i Γ⌋` bins mandated by Definition 46. Further, `TotalDeterministicBins` approximates the total deterministic bin count as `Cardinality(LargeStakeholders)`, not `Σ_i ⌊ρ_i Γ⌋`, and the assignment uses `CHOOSE` without tracking per-node floors. This deviates from Def. 46 Step 1.
  - PS‑P Step 2 (partitioning remaining stake into remaining bins according to P) and Step 3 (sample proportionally within each bin) are not modeled with stake-weighted probabilities. The current `CHOOSE v ∈ remainingNeeders : TRUE` is unweighted and does not reflect “proportional to stake.” This is a significant abstraction gap w.r.t. the distributional claims of Section 3.1 (variance reduction, Lemma 47 / Theorem 3).

- Next leader handling
  - The whitepaper states an optimization in send order: “all shred relays send their shred to the next leader first.” It does not require including the next leader among the relays. The spec imposes a stronger constraint: if `nextLeader ∈ needers` then `nextLeader ∈ psSelection` (and also assigns a bin to `nextLeader` in `PSPBinAssignment`). This biases selection and diverges from the purely randomized sampling in the paper. It can be defended as an additional modeling optimization (ensuring direct leader→nextLeader path), but it is not mandated by the whitepaper.

- Stake-based resilience checks
  - The spec adds a minimum stake constraint `CalculateStake(psSelection) ≥ RotorMinRelayStake` and defines `FailureResilient` to require that even after losing up to `RotorMaxFailedRelayStake`, remaining stake still meets `RotorMinRelayStake`. These constraints are not in the whitepaper; the paper’s success metric is purely “≥ γ correct relays with a correct leader.” The added stake thresholds are extra robustness constraints in the model.
  - Note: `RotorSelect` itself only checks the first part (≥ `RotorMinRelayStake`). The stronger `FailureResilient` condition is used in `BinCandidates` and then referenced in the witness property `RotorSelectSound`, not enforced by construction. Thus, selection may satisfy only the minimal stake check unless the invariant forces feasibility via TLC.

- Cardinality vs. Γ samples
  - The comment in the file says “picks exactly Γ relays per slice,” but `RotorSelect` returns a set of unique nodes, potentially smaller than Γ because the bin-to-relay map can assign the same node to multiple bins. This is consistent with the abstraction of sets but conflicts with the literal wording “exactly Γ” and with the paper’s notion of Γ samples (with multiplicity). The model otherwise maintains Γ bins internally.

- Domain of selection (needers)
  - The paper’s narrative implies relays are chosen from nodes that still need the slice (initially, all nodes except the leader). The guard `psSelection ⊆ needers` aligns with this. Upstream, `needers` is `Validators \ {who already have the block}` (`specs/tla/alpenglow/MainProtocol.tla:40`), matching Section 2.2.

- κ > 5/3
  - The module enforces `3*Γ > 5*γ`, modeling Lemma 7’s κ > 5/3 condition (`specs/tla/alpenglow/Rotor.tla:32-33`). This matches the whitepaper premise.

## 4. Conclusion

- Conformance (structure):
  - RotorSelect enforces relay selection from needers and is backed by a bin-based construction capturing the Γ‑bins abstraction of PS‑P. The module encodes Γ/γ and the κ > 5/3 requirement per Lemma 7.

- Deviations (semantics):
  - PS‑P Step 1 exact floors (⌊ρ_i Γ⌋) are not enforced; large stakeholders only guaranteed ≥1 bin, and the deterministic bin total is under-approximated.
  - PS‑P Steps 2–3 lack stake-proportional sampling; the current use of `CHOOSE` is unweighted and does not reflect the distributional properties claimed by Section 3.1.
  - The mandatory inclusion of `nextLeader` in the relay set is stricter than the whitepaper (which specifies a send-order optimization rather than a selection constraint).
  - The additional stake thresholds (`RotorMinRelayStake`, `RotorMaxFailedRelayStake`) are extra-model constraints absent from the paper’s Rotor success definition (Def. 6).

- Net assessment:
  - The abstraction is directionally consistent with Rotor and PS‑P at a high level (bins, Γ/γ, needers), but it diverges in key PS‑P details and adds extra constraints. It is suitable for coarse structural/safety invariants but does not faithfully model the selection distribution that underpins the whitepaper’s variance and adversarial sampling results.

## 5. Open Questions / Concerns

- PS‑P floors: Should the model enforce exact `⌊ρ_i Γ⌋` deterministic bin counts for each large stakeholder to align with Definition 46, Step 1? Current approximation can under-assign large stakeholders.
- Weighted sampling: Do we need to represent stake-weighted sampling within bins (Step 3) to justify claims tied to Lemma 47 and Theorem 3? If so, a refinement or probabilistic modeling step is needed.
- Next leader inclusion: Is forcing `nextLeader` into the relay set intended? The paper recommends prioritizing the next leader in send order, not selection. Forcing inclusion may reduce randomness and bias selection.
- Feasibility check: `PSPBinAssignmentPossible` uses `remainingBins ≤ Cardinality(remainingNeeders)`, which implies distinct assignees for remaining bins. PS‑P allows duplicates across bins. This check could be unnecessarily restrictive.
- Enforcement gap: `RotorSelect` enforces only `psSelection ⊆ needers`, a minimum stake threshold, and (forced) next leader inclusion. Structural PS‑P constraints and resilience (`ResilienceOK`) are validated in `RotorSelectSound` rather than enforced at construction; if `PSPBinAssignment` changes, soundness might be violated without a local guard.

## 6. Suggestions for Improvement

- Align PS‑P Step 1:
  - Replace `TotalDeterministicBins(needers)` with an exact sum `Σ_{v∈needers} ⌊ρ_v Γ⌋` and track per‑validator deterministic quotas; update `PSPConstraint` to require `Cardinality({j : bins[j] = v}) = ⌊ρ_v Γ⌋` for large stakeholders.

- Model stake‑weighted sampling within bins:
  - Introduce a partitioning function `P` per Definition 45 and sample from per‑bin distributions proportional to the assigned residual stake. At minimum, encode constraints that make the proportionality checkable (e.g., as a refinement relation), even if implemented nondeterministically.

- Decouple next leader optimization from selection:
  - Remove the hard constraint `(nextLeader ∈ needers ⇒ nextLeader ∈ psSelection)` from `RotorSelect`. Instead, keep `NextLeaderConstraint` as a send‑order hint or a separate predicate about delivery order/latency (`NextDisseminationDelay`). This restores unbiased sampling and matches Section 2.2.

- Strengthen construction‑time checks:
  - Have `RotorSelect` guard on structural feasibility (e.g., existence of `bins` with `StructuralBinOK` and `ResilienceOK`) rather than only post‑facto via the `RotorSelectSound` invariant. Alternatively, define `RotorSelect` to select from `BinCandidates` directly.

- Relax unnecessary uniqueness assumptions:
  - Drop or weaken `remainingBins ≤ Cardinality(remainingNeeders)` in `PSPBinAssignmentPossible` so duplicate assignments across bins are allowed, matching PS‑P’s allowance for multiplicity.

- Clarify comments and intent:
  - Update the comment “picks exactly Γ relays per slice” to reflect that the returned set may have fewer than Γ distinct relays, while bins are exactly Γ.

- Minor cleanups:
  - If `block` is unused in `RotorSelect`, either use it (e.g., to derive `needers`) or remove the parameter for clarity.

