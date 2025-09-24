# Audit: Stake Aggregation (TotalStake, CalculateStake)

## 1. Code Audited

```tla
CONSTANTS
    StakeMap        \* Function mapping validators to their stake amounts

ASSUME
    /\ StakeMap \in [Validators -> Nat \ {0}]  \* Every validator has positive stake

TotalStake == 
    LET vals == DOMAIN StakeMap
    IN IF vals = {} THEN 0
       ELSE LET RECURSIVE Sum(_)
            Sum(S) == 
                IF S = {} THEN 0
                ELSE LET v == CHOOSE x \in S : TRUE
                     IN StakeMap[v] + Sum(S \ {v})
            IN Sum(vals)

\* Calculate stake for a set of validators
CalculateStake(validatorSet) ==
    LET vals == validatorSet \cap DOMAIN StakeMap
    IN IF vals = {} THEN 0
       ELSE LET RECURSIVE Sum(_)
            Sum(S) == 
                IF S = {} THEN 0
                ELSE LET v == CHOOSE x \in S : TRUE
                     IN StakeMap[v] + Sum(S \ {v})
            IN Sum(vals)
```

- Source context in repo: `specs/tla/alpenglow/Certificates.tla:38` and `specs/tla/alpenglow/Certificates.tla:49`.

## 2. Whitepaper Sections Represented

- Stake definition and positivity (ρ_i > 0, sum to 1): `alpenglow-whitepaper.md:209` (Section 1.5 “Stake”).
- Votes and Certificates overview: `alpenglow-whitepaper.md:474` (Section 2.4).
- Certificate thresholds (80% / 60%) and cumulative stake Σ: `alpenglow-whitepaper.md:501`, `alpenglow-whitepaper.md:507` (Table 6).
- “Count once per slot” rule (used with these aggregators via UniqueValidators/StakeFromVotes): `alpenglow-whitepaper.md:513` (Def. 12) and reiterated in `alpenglow-whitepaper.md:554` (Def. 16 preface).

## 3. Reasoning and Mapping to Whitepaper

- Abstraction: StakeMap gives absolute stake weights per validator. The whitepaper defines fractional stake ρ_i > 0 that sums to 1 (alpenglow-whitepaper.md:209). Using natural numbers is an equivalent abstraction: all comparisons are scale‑invariant because thresholds are checked via `stake * 100 >= TotalStake * percent`.

- Total system stake: `TotalStake` sums over `DOMAIN StakeMap` (which equals `Validators` due to `[Validators -> Nat \ {0}]`). This models Σ_i ρ_i from Table 6. Since all stakes are positive and `Validators # {}` (see `specs/tla/alpenglow/Messages.tla:24`), `TotalStake > 0` holds.

- Subset aggregation: `CalculateStake(S)` returns Σ over validator subset S ∩ Validators. This is the primitive used wherever the paper needs Σ over a set of nodes (e.g., Σ of votes or relay sets). Order‑independence is respected; recursion removes arbitrary elements with `CHOOSE` but addition is commutative.

- Integration points implementing whitepaper logic:
  - Certificate thresholds use these aggregators via `StakeFromVotes` and `MeetsThreshold` in `specs/tla/alpenglow/Certificates.tla:60`, `:64`, `:68`. These realize Table 6’s Σ ≥ 80%/60% checks (alpenglow-whitepaper.md:501).
  - “Count once per slot” (Def. 12) is enforced by `UniqueValidators` before calling `CalculateStake` (`specs/tla/alpenglow/Certificates.tla:60`–`:65`), matching the paper’s rule that each validator contributes at most once per slot (alpenglow-whitepaper.md:513, :554).
  - Pool fallback formulas (Def. 16) are implemented using these primitives in `specs/tla/alpenglow/VoteStorage.tla:289`–`:307`, matching the exact inequalities from the whitepaper (alpenglow-whitepaper.md:554).
  - Rotor’s proportional binning uses `TotalStake` in `DeterministicBinCount` for Γ⋅ρ_i via integer division, `specs/tla/alpenglow/Rotor.tla:51`–`:53`, consistent with stake‑weighted selection (whitepaper §2.2/§3.1 commentary and PS‑P).
  - Byzantine stake bound (<20%) uses `CalculateStake`/`TotalStake` in `specs/tla/alpenglow/MainProtocol.tla:139`–`:143`, matching Assumption 1 (alpenglow-whitepaper.md:107).

## 4. Conclusion of the Audit

- Correctness: The `TotalStake` and `CalculateStake` definitions are correct, composable primitives that faithfully implement the whitepaper’s notion of cumulative stake Σ and enable percentage threshold comparisons independent of absolute scale.
- Alignment: When combined with `UniqueValidators` and `StakeFromVotes` (in the same module), they precisely enforce “count once per slot” per Definition 12 and support all certificate thresholds in Table 6, as well as fallback conditions in Definition 16.
- Sound use: These functions are referenced throughout the spec (Certificates, VoteStorage, Rotor, MainProtocol) exactly where the whitepaper requires Σ over validators or subsets, with no observable mismatches.

## 5. Open Questions / Concerns

- Finiteness assumption: The recursive `Sum` traverses a set; correctness requires finiteness of `Validators`. This holds in the top‑level spec via `Cardinality(Validators) = NumValidators` (`specs/tla/alpenglow/MainProtocol.tla:74`), but `Certificates.tla` itself does not state finiteness. It works as‑is in the composed system, but an explicit note or theorem that `DOMAIN StakeMap` is finite could make the module more self‑contained.

- Duplicate code pattern: `TotalStake` and `CalculateStake` duplicate the same recursive `Sum` pattern. This is harmless but slightly repetitive.

- Range of stakes: The model uses naturals and comparisons with `* 100`. This is fine for TLA+, but implementers should note that rational fractions map to any natural scaling. No issue in the spec, but worth calling out for readers mapping to implementation types.

## 6. Suggestions for Improvement

- Add an explicit lemma/property in `Certificates.tla`:
  - `TotalStake > 0` (follows from `Validators # {}` and positive stakes), to make preconditions more visible.
  - `TotalStake = CalculateStake(Validators)` to connect the two definitions.

- Factor the recursive sum into a single helper (optional):
  - Define `SumStake(S) == IF S = {} THEN 0 ELSE LET v == CHOOSE x \in S : TRUE IN StakeMap[v] + SumStake(S \ {v})` once, then use it in both `TotalStake` and `CalculateStake` for clarity.

- Cross‑module note (comment only): Mention that finiteness is ensured by the main protocol (`Cardinality(Validators)`) so readers of `Certificates.tla` understand recursion is well‑founded in the composed model.

- Minor readability: In `CalculateStake`, since `DOMAIN StakeMap = Validators` by assumption, `validatorSet \cap DOMAIN StakeMap` can be simplified to `validatorSet \cap Validators` (purely cosmetic).

Overall, the audited code correctly captures the whitepaper’s stake aggregation abstraction and integrates consistently across the spec where Σ and threshold checks are required.

