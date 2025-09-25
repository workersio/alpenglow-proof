# Audit: DeterministicBinCount and LargeStakeholdersInNeeders

- Code location: `specs/tla/alpenglow/Rotor.tla:52` and `specs/tla/alpenglow/Rotor.tla:56`

## 1. Code Being Audited

```tla
DeterministicBinCount(v) ==
    (StakeMap[v] * GammaTotalShreds) \div TotalStake

\* Large stakeholders: those with deterministic bin count ≥ 1
LargeStakeholdersInNeeders(needers) == 
    { v \in needers : DeterministicBinCount(v) >= 1 }
```

References in-module:
- `EXTENDS Certificates` provides `StakeMap`, `TotalStake` (see `specs/tla/alpenglow/Certificates.tla:34`, `:65`).
- `GammaTotalShreds` is a Rotor constant with assumptions (see `specs/tla/alpenglow/Rotor.tla:24`, `:30`).

## 2. Whitepaper Sections and References

- Rotor erasure coding parameters Γ and γ (total/data shreds per slice):
  - `alpenglow-whitepaper.md:380` — “For each slice, the leader generates Γ Reed–Solomon coding shreds …”
  - `alpenglow-whitepaper.md:382` — “receiving any γ shreds is enough to reconstruct the slice …”
- Relay selection domain (send to nodes that still need it; “needers” concept):
  - `alpenglow-whitepaper.md:386` — relays send to “all nodes that still need it”.
- Partition Sampling PS‑P (Smart Sampling):
  - `alpenglow-whitepaper.md:1139` — Section 3.1 Smart Sampling.
  - `alpenglow-whitepaper.md:1154-1158` — Definition 46 (PS‑P), especially Step 1:
    “For each node with relative stake ρ_i > 1/Γ, fill ⌊ρ_i·Γ⌋ bins with that node …”.

## 3. Reasoning vs. Whitepaper Claims

- Deterministic bin count formula:
  - The code computes `⌊(StakeMap[v]/TotalStake) · Γ⌋` using integer division: `(StakeMap[v] * GammaTotalShreds) \div TotalStake`.
  - This matches PS‑P Step 1’s “⌊ρ_i·Γ⌋” where `ρ_i = StakeMap[v] / TotalStake`.
  - Preconditions hold: `StakeMap ∈ [Validators → Nat\{0}]` and `GammaTotalShreds ∈ Nat \ {0}` (`specs/tla/alpenglow/Certificates.tla:37`, `specs/tla/alpenglow/Rotor.tla:30`). With any nonempty validator set, `TotalStake > 0`, so division is well-defined.
- Large stakeholder classification:
  - `LargeStakeholdersInNeeders(needers) == { v ∈ needers : DeterministicBinCount(v) ≥ 1 }` identifies nodes with at least one deterministic bin.
  - This is the natural set comprehension for the “large stakeholders” of PS‑P Step 1 (those with `⌊ρ_i·Γ⌋ ≥ 1`).
  - The filter by `needers` reflects Rotor’s operational domain: relays are selected from nodes that still need the slice (consistent with the dissemination loop; see `alpenglow-whitepaper.md:386`). At the start of dissemination for a slice, “needers” will be all nodes except the leader.
- Inequality nuance (strict vs non‑strict):
  - Whitepaper text states “for each node with relative stake ρ_i > 1/Γ fill ⌊ρ_i·Γ⌋ bins” (`:1156`). The code includes the case `ρ_i = 1/Γ` because `⌊ρ_i·Γ⌋ ≥ 1` when equal.
  - In PS‑P, Step 1 ultimately uses `⌊ρ_i·Γ⌋` bins regardless, so including the equality case is a benign strengthening aligned with the intended count; the “>” in prose is likely to emphasize that remaining stake after Step 1 is < 1/Γ.

## 4. Conclusion of the Audit

- DeterministicBinCount is correct and precisely encodes PS‑P Step 1’s bin count using TLA+ integer arithmetic.
- LargeStakeholdersInNeeders correctly captures the subset of needers that receive at least one deterministic bin under PS‑P.
- The small “> vs ≥” discrepancy at the ρ_i = 1/Γ boundary does not change the resulting deterministic bin count and is acceptable, but documenting the intent would improve clarity.
- Overall, these definitions faithfully implement the abstraction described in Section 3.1 (Definition 46, Step 1) and are consistent with Rotor’s erasure‑coding parameters from Section 2.2.

## 5. Open Questions or Concerns

- Boundary case ρ_i = 1/Γ:
  - Whitepaper uses strict “> 1/Γ”; code includes equality via `⌊ρ_i·Γ⌋ ≥ 1`. This is functionally equivalent for assigning ⌊ρ_i·Γ⌋ bins, but the classification predicate for “large” differs subtly from the prose. Consider clarifying the intended inequality in comments.
- Domain of `needers` vs leader:
  - The whitepaper describes sending to “other nodes” and relays forwarding to nodes that still need the slice. If `needers` ever includes the current leader, large‑stakeholder classification (and later selection) could select the leader as a relay, which is not intended operationally. Upstream code should ensure `leader ∉ needers` for the current slice. (See `specs/tla/alpenglow/MainProtocol.tla:425` for `needers` definition.)
- Summation vs. classification:
  - PS‑P Step 1 requires assigning exactly `⌊ρ_i·Γ⌋` bins per large stakeholder. While this block defines the count and the set of large stakeholders, other parts of the model (e.g., bin assignment) must ensure those counts are respected. In the current module, `TotalDeterministicBins` uses a conservative approximation, which may undercount in some states. This is beyond the scope of the present block but worth tracking for full PS‑P fidelity.

## 6. Suggestions for Improvement

- Comment precision: Amend the comment above `LargeStakeholdersInNeeders` to note that equality ρ_i = 1/Γ is included (since `⌊ρ_i·Γ⌋ ≥ 1`), and reference `alpenglow-whitepaper.md:1156` explicitly for PS‑P Step 1.
- Defensive assumption: Optionally document that `Validators ≠ {}` (already implied where used) so `TotalStake > 0` holds when `DeterministicBinCount` is applied.
- Consistency check: Ensure upstream `needers` excludes the current leader for the slice to align with `alpenglow-whitepaper.md:384-386`. If not already enforced elsewhere, consider filtering `needers` by removing the leader at the call site.

```text
File references for traceability:
- specs/tla/alpenglow/Rotor.tla:52, :56
- specs/tla/alpenglow/Certificates.tla:34, :65
- alpenglow-whitepaper.md:380, :382, :386, :1139, :1154-:1158
```
