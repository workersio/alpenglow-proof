# Audit: NextLeaderConstraint, ExactBinAssignmentConstraint, NonEmptyConstraint (Rotor)

## 1. Code Being Audited

```tla
NextLeaderConstraint(bins, needers, nextLeader) ==
    (nextLeader \in needers => \E j \in DOMAIN bins : bins[j] = nextLeader)

\* Exact bin assignment constraint - exactly Γ bins assigned
ExactBinAssignmentConstraint(bins) == DOMAIN bins = 1..GammaTotalShreds

\* Basic non-empty requirement when dissemination needed
NonEmptyConstraint(bins, needers) == 
    (needers # {} => DOMAIN bins # {})
```

Definitions appear in: `specs/tla/alpenglow/Rotor.tla:143`, `specs/tla/alpenglow/Rotor.tla:147`, `specs/tla/alpenglow/Rotor.tla:150`.

Related usage/context:
- `StructuralBinOK(bins, needers, nextLeader)`: `specs/tla/alpenglow/Rotor.tla:154`
- `BinCandidates` and `RotorBinAssignmentPossible` consume `StructuralBinOK`: `specs/tla/alpenglow/Rotor.tla:165`, `specs/tla/alpenglow/Rotor.tla:172`
- `needers` is defined where Rotor is invoked: `specs/tla/alpenglow/MainProtocol.tla:425`
- `nextLeader` is produced via `Leader(nextSlot)`: `specs/tla/alpenglow/MainProtocol.tla:432`
- `GammaTotalShreds` is a Rotor constant with assumptions: `specs/tla/alpenglow/Rotor.tla:24`, `specs/tla/alpenglow/Rotor.tla:30`

## 2. Whitepaper Sections and References

- Erasure coding parameters (Γ, γ) and over-provisioning context: `alpenglow-whitepaper.md:265`
- Rotor slice/relay sampling overview (Γ shreds per slice; relays sampled per slice): `alpenglow-whitepaper.md:384`
- “Next leader first” optimization (send-order, not selection): `alpenglow-whitepaper.md:386`
- PS‑P (partition sampling) definition for relay selection:
  - Section header: `alpenglow-whitepaper.md:1139`
  - Definition 46 (Steps 1–3): `alpenglow-whitepaper.md:1154`

## 3. Reasoning: What the Code Means vs. What the Paper Claims

- NextLeaderConstraint
  - Code: If the next leader still needs the block, require that it appears in at least one bin (i.e., be selected as one of the Γ relays).
  - Paper: “As a minor optimization, all shred relays send their shred to the next leader first.” This is a delivery ordering policy for receivers; it does not require selecting the next leader as a relay. See `alpenglow-whitepaper.md:386`.
  - Assessment: The code turns a send-order optimization into a hard selection constraint, which is stricter than the whitepaper and distorts PS‑P’s sampling distribution by deterministically forcing inclusion when `nextLeader ∈ needers`.

- ExactBinAssignmentConstraint
  - Code: Enforces `DOMAIN bins = 1..GammaTotalShreds` (exactly Γ bins assigned).
  - Paper: For each slice there are Γ shreds; the leader samples Γ relays per slice (one per shred). See `alpenglow-whitepaper.md:265`, `alpenglow-whitepaper.md:384`.
  - Assessment: Correct abstraction. It aligns with “Γ coding shreds per slice,” each routed to some relay.

- NonEmptyConstraint
  - Code: If `needers ≠ {}`, require `DOMAIN bins ≠ {}`.
  - Paper: No explicit statement, but the spirit is that a slice to be disseminated uses Γ relays. Given Rotor’s assumptions include `GammaTotalShreds ∈ Nat \ {0}` (`specs/tla/alpenglow/Rotor.tla:30`) and the spec elsewhere already requires `DOMAIN bins = 1..GammaTotalShreds`, this predicate is redundant.
  - Assessment: Redundant under the Γ-domain constraint. Harmless but unnecessary in the presence of `ExactBinAssignmentConstraint` and the Γ>0 assumption.

## 4. Conclusion of the Audit

- ExactBinAssignmentConstraint faithfully captures the whitepaper’s requirement that each slice uses exactly Γ relay assignments.
- NonEmptyConstraint is redundant given the Γ-domain constraint and assumptions (`GammaTotalShreds > 0`). It does not contradict the paper, but it adds no value if exact-domain is required elsewhere.
- NextLeaderConstraint does not reflect the whitepaper precisely. The whitepaper specifies a send-order optimization (“relays send to the next leader first”), not a selection rule requiring the next leader to be one of the Γ relays. Encoding it as a hard selection constraint deviates from PS‑P and can bias or reduce the feasible PS‑P assignments.

## 5. Open Questions or Concerns

- Intentional design choice? Is the goal to force the next leader to be a relay for each slice whenever it still needs the block? If so, this differs from the paper and should be documented as an intentional deviation (with rationale and impact on PS‑P distribution fairness and feasibility).
- Interplay with PS‑P: Under PS‑P (Def. 46), bins and selections are stake‑proportional. Forcing one specific node (the next leader) into the selection perturbs the distribution. Is that acceptable for the intended analysis (e.g., liveness/latency modeling) and are safety proofs unaffected?
- Redundancy: `ExactBinAssignmentConstraint` already enforces a non‑empty domain when Γ>0. Do we want to keep `NonEmptyConstraint` merely as a readability guard, or remove it to reduce duplication?
- Consistency with other “next‑leader” abstractions: `NextDisseminationDelay(sample, nextLeader)` in Rotor is defined as `0` iff `nextLeader ∈ sample` (`specs/tla/alpenglow/Rotor.tla:224`), again tying delay to the next leader being a relay. The whitepaper’s optimization lowers the next leader’s receive latency regardless of whether the next leader is itself a relay.

## 6. Suggestions for Improvement

- Model “next leader first” as a delivery/latency property, not a selection constraint:
  - Remove `NextLeaderConstraint` from `StructuralBinOK`. Keep PS‑P constraints purely about correctness of sampling/assignment.
  - Express the optimization as a separate latency relation over message deliveries (e.g., receivers’ ordering or per‑receiver delay bounds), independent of whether the next leader is a relay.
  - If a hint is desired without forcing selection, introduce an optional preference relation (tie‑breaker) at selection time but do not make it a hard constraint.

- Simplify constraints:
  - Drop `NonEmptyConstraint` if `ExactBinAssignmentConstraint` (and Γ>0 assumption) is always enforced where bins are considered.
  - Avoid duplicating the exact-domain check: ensure it is enforced in exactly one place (e.g., inside `PSPConstraint` or `StructuralBinOK`), and reference that predicate consistently.

- Documentation:
  - If the design intentionally forces the next leader to be a relay, add a comment with a whitepaper deviation note in `Rotor.tla` near `NextLeaderConstraint` explaining the trade‑off (latency vs. distribution fidelity) and where proofs rely on it.

## Cross‑References (TLA Sources)

- Code under audit: `specs/tla/alpenglow/Rotor.tla:143`, `specs/tla/alpenglow/Rotor.tla:147`, `specs/tla/alpenglow/Rotor.tla:150`
- Structural wrapper: `specs/tla/alpenglow/Rotor.tla:154`
- Constants/assumptions (Γ, γ): `specs/tla/alpenglow/Rotor.tla:24`, `specs/tla/alpenglow/Rotor.tla:30`
- Needers/nextLeader computed at call sites: `specs/tla/alpenglow/MainProtocol.tla:425`, `specs/tla/alpenglow/MainProtocol.tla:432`

## Cross‑References (Whitepaper)

- Erasure code and parameters (Γ, γ, κ): `alpenglow-whitepaper.md:265`
- Per‑slice sampling of relays: `alpenglow-whitepaper.md:384`
- “Next leader first” optimization (send‑order): `alpenglow-whitepaper.md:386`
- PS‑P (partition sampling) Step 1–3 definition: `alpenglow-whitepaper.md:1154`

