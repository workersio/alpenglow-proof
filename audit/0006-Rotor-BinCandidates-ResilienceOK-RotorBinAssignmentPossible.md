**Code Under Audit**

```
ResilienceOK(sample) == FailureResilient(sample)

\* Core candidate bin assignments following whitepaper constraints
BinCandidates(block, needers, nextLeader) ==
    { bins \in [1..GammaTotalShreds -> needers] : 
        /\ StructuralBinOK(bins, needers, nextLeader)
        /\ ResilienceOK(BinsToRelaySet(bins)) }


\* Feasibility predicate: some structurally valid bin assignment exists when needed
RotorBinAssignmentPossible(block, needers, nextLeader) ==
    IF needers = {} THEN TRUE ELSE BinCandidates(block, needers, nextLeader) # {}
```

**Whitepaper References**

- Erasure coding and constants (Γ, γ, κ):
  - `alpenglow-whitepaper.md:265` defines a (Γ, γ) erasure code; `:267` defines expansion ratio κ = Γ/γ.
  - Rotor resilience requires κ > 5/3 (Lemma 7): `alpenglow-whitepaper.md:418`.
- Rotor relay sampling (PS-P):
  - PS-P definition and 3-step procedure (Definition 46): `alpenglow-whitepaper.md:1154`.
- Latency hint “send to next leader first”: `alpenglow-whitepaper.md:386`.

Related TLA+ definitions this code depends on (directly or transitively):

- `GammaTotalShreds`, `GammaDataShreds` and κ > 5/3 assumption: `specs/tla/alpenglow/Rotor.tla:24`, `:25`, `:32`.
- `BinsToRelaySet`: converts a bin function into a set of relays: `specs/tla/alpenglow/Rotor.tla:112`.
- `StructuralBinOK`: bundles structural constraints, including PS-P shape and next‑leader priority: `specs/tla/alpenglow/Rotor.tla:154`.
  - `PSPConstraint`: structural PS-P check: `specs/tla/alpenglow/Rotor.tla:136`.
  - `ExactBinAssignmentConstraint`: exact Γ bins: `specs/tla/alpenglow/Rotor.tla:147`.
  - `NextLeaderConstraint`: next leader included if needed: `specs/tla/alpenglow/Rotor.tla:141` (via the combined predicate at `:154`).
- `FailureResilient`: stake-based residual resilience used by `ResilienceOK`: `specs/tla/alpenglow/Rotor.tla:125`.
  - Uses `CalculateStake` from certificates: `specs/tla/alpenglow/Certificates.tla:76`.

**Reasoning and Alignment With Whitepaper**

- Intent of the audited code
  - `BinCandidates` characterizes the set of all bin functions (one assignee per bin 1..Γ) that satisfy the Rotor structural rules and an additional resilience filter. It is used as a feasibility/existence witness via `RotorBinAssignmentPossible`.
  - `ResilienceOK` is a synonym for `FailureResilient`, i.e., it requires selected relays to have enough total stake, and enough residual stake after bounded failures.

- Structural constraints vs PS-P (Definition 46)
  - Whitepaper Step 1 requires that each node with ρ_i > 1/Γ occupies exactly ⌊ρ_i·Γ⌋ bins deterministically; remaining bins are filled by partitioning and per‑bin sampling (Steps 2–3).
  - In TLA, this structure is represented by bin functions and checked by `StructuralBinOK`/`PSPConstraint`. However, the current constraint only enforces “every large stakeholder gets ≥1 bin,” not “≥⌊ρ_i·Γ⌋ bins.” See `specs/tla/alpenglow/Rotor.tla:136`.
  - Consequence: `BinCandidates` may include assignments that under‑allocate bins to very large stakeholders relative to Step 1.

- Erasure coding parameters and success conditions
  - The Rotor module assumes κ > 5/3 (`3·Γ > 5·γ`) matching Lemma 7 (rotor resilience). See `specs/tla/alpenglow/Rotor.tla:32` and `alpenglow-whitepaper.md:418`.
  - Although not directly referenced here, the model’s `SliceReconstructable(receivedShredsCount) == receivedShredsCount ≥ γ` aligns with the decode threshold for Reed–Solomon codes (`alpenglow-whitepaper.md:265`, `:267`).

- Next leader prioritization
  - `StructuralBinOK` includes `NextLeaderConstraint`, which ensures the next leader appears among chosen relays when it still needs the block, aligning with the whitepaper’s minor optimization to “send to the next leader first” (`alpenglow-whitepaper.md:386`).

- ResilienceOK vs whitepaper
  - `ResilienceOK(BinsToRelaySet(bins))` introduces a stake‑based resilience guard that is not explicitly specified in the whitepaper. The paper’s Rotor success is phrased in terms of γ correct relays and κ (Lemma 7), and PS-P is analyzed probabilistically (Lemma 47, Theorem 3). The stake‑coverage guard is a modeling addition for robustness, not a direct whitepaper requirement.

**Conclusion**

- Correct high‑level abstraction:
  - Modeling relay selection as bin functions `[1..Γ → needers]` matches whitepaper PS-P’s “one sample per bin” abstraction. Ensuring the domain is exactly 1..Γ, values lie within `needers`, and prioritizing the next leader are all consistent with §2.2 and §3.1.
  - The κ > 5/3 assumption is consistent with Lemma 7’s over‑provisioning requirement.

- Primary deviation from the whitepaper:
  - The structural constraint does not enforce the exact deterministic bin count from Step 1 of Definition 46. It only guarantees ≥1 bin per large stakeholder, whereas the paper requires ≥⌊ρ_i·Γ⌋ bins for each such stakeholder. Thus, `BinCandidates` may accept assignments that the PS-P procedure would not produce.

- Additional modeling guard:
  - `ResilienceOK` adds a stake‑residual condition absent from the whitepaper. While conservative and possibly useful for robustness, it should be explicitly documented as an assumption beyond the paper.

**Open Questions / Concerns**

- Deterministic bin counts:
  - Should `PSPConstraint` require `Cardinality({j | bins[j] = v}) ≥ DeterministicBinCount(v)` for all `v` with `DeterministicBinCount(v) ≥ 1`? Current ≥1 is too weak relative to Definition 46 Step 1.

- Completeness of candidate set vs actual PS-P:
  - `BinCandidates` uses structural predicates rather than the specific PS-P construction. Is the intent to over‑approximate all structurally valid assignments for feasibility checks only, or should it capture exactly those realizable by the PS-P algorithm? If the latter, constraints need strengthening.

- Unused `block` parameter:
  - `block` is not consumed by the predicates. Is it intended to scope additional constraints (e.g., slice index, block metadata), or can it be removed?

- Resilience guard semantics:
  - The thresholds `RotorMinRelayStake` and `RotorMaxFailedRelayStake` are not tied to whitepaper parameters. What values are intended, and how do they relate to κ, γ, and the PS-P failure probabilities (Lemma 47, Theorem 3)?

**Suggestions for Improvement**

- Strengthen PS-P structural compliance:
  - Update `PSPConstraint` to encode Definition 46 Step 1:
    - Require for all `v` with `DeterministicBinCount(v) ≥ 1` that `Cardinality({j ∈ DOMAIN bins : bins[j] = v}) ≥ DeterministicBinCount(v)`.
  - Optionally, add a bound on total deterministic bins: `Σ_v DeterministicBinCount(v) ≤ Γ` and ensure these bins are filled before any remaining bins are assigned.

- Clarify intent of `BinCandidates`:
  - If the goal is feasibility/existence irrespective of the exact PS-P procedure, document it as an over‑approximation. Otherwise, refine constraints to match PS-P more closely (e.g., model the partitioning step as an abstract predicate, and require that remaining bins’ assignments are consistent with some partition of residual stakes).

- Document non‑paper resilience guard:
  - State explicitly that `ResilienceOK` is an additional model guard for robustness. Provide guidance for setting `RotorMinRelayStake` and `RotorMaxFailedRelayStake`, or tie them to whitepaper parameters (e.g., target stake coverage to balance expected γ‑correct relays).

- Remove or use the `block` parameter:
  - If unused, remove it for clarity. If kept, document its intended use (e.g., to reference per‑slice indices or block metadata in future constraints).

- Minor: `NonEmptyConstraint` may be redundant when `ExactBinAssignmentConstraint` is required; consider simplifying `StructuralBinOK` to avoid duplication.

**Key File References**

- `specs/tla/alpenglow/Rotor.tla:162` ResilienceOK alias.
- `specs/tla/alpenglow/Rotor.tla:165` BinCandidates definition.
- `specs/tla/alpenglow/Rotor.tla:172` RotorBinAssignmentPossible definition.
- `specs/tla/alpenglow/Rotor.tla:112` BinsToRelaySet definition.
- `specs/tla/alpenglow/Rotor.tla:154` StructuralBinOK composition of constraints.
- `specs/tla/alpenglow/Rotor.tla:136` PSPConstraint (currently ≥1 bin for large stakeholders only).
- `specs/tla/alpenglow/Rotor.tla:52` DeterministicBinCount and stake basis.
- `specs/tla/alpenglow/Certificates.tla:76` CalculateStake used by FailureResilient.
- `alpenglow-whitepaper.md:418` Lemma 7 (κ > 5/3 rotor resilience).
- `alpenglow-whitepaper.md:1154` Definition 46 (PS-P sampling, Steps 1–3).
- `alpenglow-whitepaper.md:386` Next leader prioritization.

