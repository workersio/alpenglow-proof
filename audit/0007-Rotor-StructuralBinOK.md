# Audit: Rotor.StructuralBinOK

1. Code under audit

```
StructuralBinOK(bins, needers, nextLeader) ==
    /\ ExactBinAssignmentConstraint(bins)        \* Exactly Γ bins (Section 2.2)
    /\ PSPConstraint(bins, needers)              \* PS-P compliance (§3.1)
    /\ NextLeaderConstraint(bins, needers, nextLeader)  \* Optimization hint
    /\ NonEmptyConstraint(bins, needers)
```

Key references in codebase:

- `specs/tla/alpenglow/Rotor.tla:146` ExactBinAssignmentConstraint(bins) == DOMAIN bins = 1..GammaTotalShreds
- `specs/tla/alpenglow/Rotor.tla:135` PSPConstraint(bins, needers)
- `specs/tla/alpenglow/Rotor.tla:143` NextLeaderConstraint(bins, needers, nextLeader)
- `specs/tla/alpenglow/Rotor.tla:150` NonEmptyConstraint(bins, needers)
- `specs/tla/alpenglow/Rotor.tla:51` DeterministicBinCount(v) == (StakeMap[v] * GammaTotalShreds) \div TotalStake
- `specs/tla/alpenglow/Rotor.tla:132` LargeStakeholders(S) == { v \in S : DeterministicBinCount(v) >= 1 }
- `specs/tla/alpenglow/Certificates.tla:65` TotalStake definition

2. Whitepaper sections and references represented

- Section 2.2 Rotor (erasure coding; Γ shreds per slice, γ needed to reconstruct)
  - `alpenglow-whitepaper.md:365` “2.2 Rotor”
  - `alpenglow-whitepaper.md:380` “For each slice, the leader generates Γ shreds …”
  - `alpenglow-whitepaper.md:265–267` Erasure code, κ = Γ/γ
- Section 3.1 Smart Sampling (PS-P)
  - `alpenglow-whitepaper.md:1154` Definition 46 (PS-P), Steps 1–3
  - `alpenglow-whitepaper.md:1164–1177` Lemma 47, Theorem 3 (variance reduction vs IID/FA1-IID)
- Next-leader latency hint
  - `alpenglow-whitepaper.md:386` “As a minor optimization, all shred relays send their shred to the next leader first.”

3. Reasoning: what the code asserts vs whitepaper claims

- Exact bin count (Γ):
  - Code: `ExactBinAssignmentConstraint(bins)` and the first conjunct in `PSPConstraint` both enforce `DOMAIN bins = 1..GammaTotalShreds` (see `specs/tla/alpenglow/Rotor.tla:146,135–137`).
  - Whitepaper: Section 2.2 mandates Γ shreds per slice; structurally one relay per bin is intended.
  - Assessment: Correct and faithful. Minor duplication exists (both `ExactBinAssignmentConstraint` and `PSPConstraint` restate the same domain equality).

- PS-P compliance (bin assignment and large stakeholders):
  - Whitepaper (Def. 46):
    - Step 1: For each node with ρ_i > 1/Γ, deterministically fill ⌊ρ_i·Γ⌋ bins with that node; residual stake ρ'_i < 1/Γ.
    - Step 2: Partition the residual stakes across the remaining k = Γ − Σ_i ⌊ρ_i·Γ⌋ bins.
    - Step 3: From each remaining bin, sample one node proportional to stake.
  - Code: `PSPConstraint(bins, needers)` asserts:
    - Exactly Γ bins (again), all assignments map to `needers`.
    - For each v in `LargeStakeholders(needers)` (i.e., DeterministicBinCount(v) ≥ 1), v appears in the assignment at least once: `Cardinality({j : bins[j] = v}) ≥ 1` (`specs/tla/alpenglow/Rotor.tla:135–141`).
  - Assessment:
    - The ≥1 lower bound for large stakeholders is weaker than Step 1 of PS-P. Def. 46 implies v must occupy at least ⌊ρ_i·Γ⌋ bins deterministically; the code only demands “≥ 1” regardless of whether ⌊ρ_i·Γ⌋ = 2, 3, …
    - A structurally faithful abstraction would assert `Cardinality({j : bins[j] = v}) ≥ DeterministicBinCount(v)` for all v (allowing extra occurrences to come from Step 3). The current constraint therefore under-specifies the deterministic multiplicity requirement.
    - The structure does not attempt to encode Step 2’s partitioning or Step 3’s proportional sampling, which is acceptable in an abstract structural predicate—but the deterministic multiplicity (Step 1) should still be captured.

- Next leader optimization:
  - Whitepaper: Relays “send to the next leader first” as a transmission ordering optimization (alpenglow-whitepaper.md:386). It does not require the next leader to be one of the Γ selected relays.
  - Code: `NextLeaderConstraint(bins, needers, nextLeader)` requires inclusion of `nextLeader` in some bin whenever `nextLeader ∈ needers` (`specs/tla/alpenglow/Rotor.tla:143–145`). This is a selection constraint, not merely an ordering hint.
  - Assessment: This is stronger than the whitepaper. It enforces inclusion of the next leader among the Γ “bin winners,” whereas the whitepaper only stipulates that relays prioritize sending to the next leader (who may or may not be a relay). As a result, the spec diverges from the source of truth by baking an optimization into correctness.

- Non-empty constraint:
  - Code: `NonEmptyConstraint(bins, needers) == (needers # {} => DOMAIN bins # {})` (`specs/tla/alpenglow/Rotor.tla:150–151`). Given `ASSUME GammaTotalShreds ∈ Nat \ {0}` and `ExactBinAssignmentConstraint`, the domain is always non-empty; thus this conjunct is redundant under the module assumptions.
  - Assessment: Harmless but unnecessary.

4. Conclusion

- Exact Γ-bins requirement matches Section 2.2. Good.
- PS-P compliance is only partially captured. The structural constraint fails to require the correct deterministic multiplicity (at least ⌊ρ_i·Γ⌋ occurrences) for large stakeholders per Definition 46 Step 1. This materially weakens the variance-reduction guarantee that PS-P provides in the whitepaper.
- Next leader constraint is stronger than the whitepaper. It turns a latency optimization (send-first policy) into a mandatory selection inclusion, which is not stated in the paper and may have unintended effects on stake fairness or resilience.
- Non-empty constraint is redundant.

Net: StructuralBinOK, as written, is not fully faithful to Def. 46 and encodes an extra optimization as a correctness condition. It should be adjusted to align precisely with the whitepaper abstractions.

5. Open questions / concerns

- Should the structural predicate enforce the deterministic multiplicity lower bound exactly as ⌊ρ_i·Γ⌋ for every node, i.e., `∀v: count_v ≥ DeterministicBinCount(v)`? This seems necessary to reflect Def. 46 Step 1.
- Is inclusion of the next leader among Γ relays actually a protocol requirement, or is it purely an ordering hint for transmissions? The whitepaper suggests the latter.
- The code duplicates the `DOMAIN bins = 1..GammaTotalShreds` condition in both `ExactBinAssignmentConstraint` and `PSPConstraint`. Is this duplication intentional for readability, or should one be removed to avoid confusion?
- The bin-assignment feasibility predicate elsewhere (`PSPBinAssignmentPossible`) constrains `remainingBins <= Cardinality(remainingNeeders)`. PS-P does not require unique nodes per bin in Steps 2–3; duplicates are allowed across bins. Is this additional feasibility guard intended?

6. Suggestions for improvement

- Enforce deterministic multiplicity from PS-P Step 1:
  - Strengthen `PSPConstraint` to require, for all validators v in `needers`, `Cardinality({j : bins[j] = v}) ≥ DeterministicBinCount(v)`. This captures the lower bound implied by Step 1 and permits additional occurrences from Step 3.

- Relax next leader inclusion to match the whitepaper:
  - Replace `NextLeaderConstraint` with a non-mandatory latency hint. For example, keep `NextDisseminationDelay(sample, nextLeader)` or add a liveness/latency invariant that references sending to `nextLeader` first when present, without enforcing that the next leader must be among the Γ relays.

- Remove redundancy:
  - Drop `NonEmptyConstraint` (it follows from `GammaTotalShreds > 0` and `ExactBinAssignmentConstraint`).
  - Consider removing the duplicate `DOMAIN bins = 1..GammaTotalShreds` from `PSPConstraint` if `ExactBinAssignmentConstraint` is always conjoined.

- Documentation alignment:
  - In comments near `PSPConstraint`, explicitly cite PS-P Definition 46 Step 1 and clarify that the constraint encodes its deterministic lower bound; note that Steps 2–3 are probabilistic and are not encoded as structural invariants.

- Optional: model partitioning abstractly (if desired):
  - Add a predicate `PartitionsOK(needers, bins)` that states: there exists some partitioning P over the remaining k bins and a sampling outcome consistent with P such that the chosen `bins` could arise. This preserves abstraction while documenting the connection to Def. 46 Steps 2–3.

References (file anchors)

- Rotor module: `specs/tla/alpenglow/Rotor.tla:135`, `:143`, `:146`, `:150`, `:154`
- Stake map and totals: `specs/tla/alpenglow/Certificates.tla:65`, `:76`
- Whitepaper Rotor §2.2: `alpenglow-whitepaper.md:365`, `:380`, `:265`
- Whitepaper PS-P Def. 46: `alpenglow-whitepaper.md:1154`
- Whitepaper next-leader hint: `alpenglow-whitepaper.md:386`

