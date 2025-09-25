# Rotor: Constants and Assumptions — Audit

1. Code that you are auditing.

```
CONSTANTS
    RotorMinRelayStake,   \* Minimum total stake covered by a relay set
    GammaTotalShreds,       \* Γ > 0 - exactly this many relays per slice
    GammaDataShreds,        \* γ > 0 - minimum shreds needed to reconstruct
    RotorMaxFailedRelayStake, \* Upper bound (stake) of relays that may fail (crash/Byz)
    MaxSlicesPerBlock

ASSUME
    /\ GammaTotalShreds \in Nat \ {0}
    /\ GammaDataShreds \in Nat \ {0}
    /\ 3 * GammaTotalShreds > 5 * GammaDataShreds   \* κ > 5/3 resilience condition (Lemma 7)
    /\ GammaDataShreds < GammaTotalShreds
    /\ RotorMinRelayStake \in Nat \ {0}
    /\ RotorMinRelayStake <= TotalStake
    /\ RotorMaxFailedRelayStake \in Nat
    /\ RotorMaxFailedRelayStake < RotorMinRelayStake   \* Need residual stake after failures
    /\ MaxSlicesPerBlock \in Nat \ {0}
```

File context: `specs/tla/alpenglow/Rotor.tla:22–38`. Module extends: `EXTENDS Naturals, FiniteSets, Certificates` (`specs/tla/alpenglow/Rotor.tla:3`).


2. The whitepaper section and references that the code represents.

- Erasure coding and data expansion: `(Γ, γ)` Reed–Solomon and `κ = Γ/γ` in `alpenglow-whitepaper.md:267`.
- Rotor success condition (requires correct leader and ≥ γ correct relays): `alpenglow-whitepaper.md:414` (Definition 6).
- Rotor resilience (asymptotic success if κ > 5/3): `alpenglow-whitepaper.md:418` (Lemma 7).
- Latency and effect of over-provisioning κ (context): `alpenglow-whitepaper.md:412, 431` (Figure 4 caption; Lemma 8).
- Slices and shreds (block structure and pipelining): `alpenglow-whitepaper.md:55` and block definition in `alpenglow-whitepaper.md:351` (Definition 3).
- Sampling scheme PS-P (binning and stake-proportional sampling; context for Γ relays): `alpenglow-whitepaper.md:1154–1158` (Definition 46).
- Extra crash tolerance (contextual rationale for modeling crash budget): `alpenglow-whitepaper.md:122` (Assumption 2).

Cross-module references in the TLA+ code:

- `TotalStake` and `StakeMap` are defined in `specs/tla/alpenglow/Certificates.tla:33–36, 65` (StakeMap constant and TotalStake operator). Rotor correctly imports them via `EXTENDS Certificates`.
- Standard sets/operators (`Nat`) from `Naturals` and finite set constructs from `FiniteSets`.
- Concrete model values for these constants are provided in `specs/tla/alpenglow/MC.cfg:30–36` (e.g., `GammaTotalShreds = 6`, `GammaDataShreds = 3`, `RotorMinRelayStake = 40`).


3. The reasoning behind the code and what the whitepaper claims.

- Γ and γ are positive naturals; γ < Γ.
  - The assumptions `GammaTotalShreds ∈ Nat \ {0}`, `GammaDataShreds ∈ Nat \ {0}`, and `GammaDataShreds < GammaTotalShreds` encode the prerequisites for a `(Γ, γ)` Reed–Solomon code where any γ of Γ shreds reconstruct a slice (`alpenglow-whitepaper.md:267`).

- κ > 5/3 encoded arithmetically as `3*Γ > 5*γ`.
  - This matches Lemma 7’s resilience requirement (`alpenglow-whitepaper.md:418`), which asserts that with κ > 5/3 and γ → ∞, a slice is received correctly with probability 1 (assuming the leader is correct). The arithmetic form avoids rationals, consistent with Rotor’s code comment.

- Rotor success condition depends on γ correct relays, not on stake thresholds.
  - Definition 6 (`alpenglow-whitepaper.md:414`) defines success when the leader is correct and at least γ relays are correct. The assumptions here establish the parameters needed to express γ and Γ correctly elsewhere in the module (e.g., for predicates like `SliceReconstructable` and `RotorSuccessful`), and the ratio κ.

- Stake-based parameters for robustness: `RotorMinRelayStake`, `RotorMaxFailedRelayStake`.
  - These parameters are not explicitly prescribed by the whitepaper for Rotor’s basic success semantics. They appear in the TLA+ spec to strengthen selection validity and to model a stake-budget for failures in relay sets (later used by `FailureResilient(sample)`), aligning with the paper’s broader “20+20” resilience narrative and Assumption 2 (`alpenglow-whitepaper.md:122`) but going beyond Definition 6.
  - The constraints `RotorMinRelayStake ∈ Nat \ {0}`, `RotorMinRelayStake ≤ TotalStake`, and `RotorMaxFailedRelayStake < RotorMinRelayStake` guarantee that: (i) the min-stake target is well-formed and feasible w.r.t. the system’s total stake, and (ii) after losing up to the bounded failed-relay stake, the residual can still meet the minimum stake target (as enforced later in the module).

- `MaxSlicesPerBlock ∈ Nat \ {0}`
  - Whitepaper uses an abstract “k slices per block” for pipelining (`alpenglow-whitepaper.md:55, 351, 752`), without a specific bound. The TLA+ assumption simply models that there is at least one slice per block in the parameterized model; it does not contradict the paper.


4. The conclusion of the audit.

- The constants and their domains match the whitepaper’s Rotor abstraction of erasure coding and slice reconstruction.
- The inequality `3*GammaTotalShreds > 5*GammaDataShreds` exactly encodes Lemma 7’s κ > 5/3 requirement (`alpenglow-whitepaper.md:418`). This is consistent with the paper’s recommended κ=2 elsewhere (suggested setting, `alpenglow-whitepaper.md:173`), which satisfies the inequality.
- The use of `TotalStake` from Certificates is correct and consistent across modules; Rotor’s `EXTENDS Certificates` provides the needed `StakeMap` and `TotalStake` definitions (`specs/tla/alpenglow/Certificates.tla:65`).
- The stake-based parameters (`RotorMinRelayStake`, `RotorMaxFailedRelayStake`) are additional modeling knobs not mandated by Definition 6. They strengthen the selection criteria in the TLA+ model for resilience under failures and do not contradict the whitepaper; however, they should be understood as extra to the paper’s minimum success condition.
- `MaxSlicesPerBlock` is a benign modeling parameter consistent with the paper’s notion of slices per block.


5. Any open questions or concerns.

- Whitepaper tie-in for stake thresholds:
  - The paper’s Rotor success condition is purely “≥ γ correct relays with a correct leader” (`alpenglow-whitepaper.md:414`). The TLA+ spec introduces `RotorMinRelayStake` and `RotorMaxFailedRelayStake` constraints. These appear to be extra safety/robustness constraints. It would help to explicitly link them to a whitepaper assumption or lemma (e.g., Assumption 2 on extra crash tolerance, `alpenglow-whitepaper.md:122`) or to a concrete reliability target so readers understand their role.

- Asymptotic lemma vs finite models:
  - Lemma 7’s guarantee is asymptotic in γ. The TLA+ spec uses only the κ > 5/3 ratio, not an absolute lower bound on γ. When model-checking with small γ (e.g., γ=3 in `MC.cfg`), Rotor success is probabilistic in the paper’s analysis but must be reasoned about non-probabilistically in the spec. This is acceptable at the abstraction level, but worth noting as a modeling mismatch (probabilistic guarantee vs. deterministic spec parameters).

- Terminology alignment:
  - The comments reference “Lemma 7” correctly, but if the whitepaper’s numbering changes, the TLA+ comment should be kept in sync.


6. Any suggestions for improvement.

- Document the extra stake thresholds:
  - Add a short comment in `Rotor.tla` by the `ASSUME` block (or near `FailureResilient`) that these stake constraints are a modeling strengthening for failure robustness, and optionally cite Assumption 2 (`alpenglow-whitepaper.md:122`).

- Optional explicit κ operator (commented):
  - While the spec avoids rationals, consider adding a commented helper `\* KappaExpRatio == GammaTotalShreds / GammaDataShreds` with a note that the inequality `3*Γ > 5*γ` is the integer form of `κ > 5/3` per Lemma 7.

- Cross-reference slices:
  - Next to `MaxSlicesPerBlock`, add a reference to the block/slice definitions (`alpenglow-whitepaper.md:351` and pipelining context at `alpenglow-whitepaper.md:55`) for quick reader orientation.

- Model-guide for configurations:
  - In `MC.cfg`, add a comment that the picked `(Γ, γ)` should satisfy `3Γ > 5γ` (e.g., Γ=6, γ=3 → κ=2) and that larger γ increases the margin consistent with the probabilistic analysis.

Metadata and pointers:

- Source code: `specs/tla/alpenglow/Rotor.tla:22–38`, `specs/tla/alpenglow/Rotor.tla:3`.
- External defs: `specs/tla/alpenglow/Certificates.tla:33–36, 65`.
- Model params: `specs/tla/alpenglow/MC.cfg:30–36`.
- Paper anchors: `alpenglow-whitepaper.md:267, 351, 412, 414, 418, 431, 1154–1158, 122`.

