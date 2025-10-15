---------------------------- MODULE Rotor ----------------------------
(*
  This module formalizes Rotor relay sampling and success conditions
  exactly as in Alpenglow. References are to the white paper sections.
  For erasure coding notation (Γ,γ) and κ = Γ/γ see §1.6 “Erasure Code”. :contentReference[oaicite:0]{index=0}
  Rotor description and success criterion are in §2.2, Def. 6, Lemma 7. :contentReference[oaicite:1]{index=1}
  PS‑P sampling is in §3.1, Defs. 45–46, Thm. 3. :contentReference[oaicite:2]{index=2}
*)

EXTENDS Naturals, FiniteSets, Certificates

(*
  Constants:
   - Γ = total shreds/relays per slice (GammaTotalShreds)
   - γ = min shreds to reconstruct (GammaDataShreds)
  Constraints match erasure coding and Rotor resilience κ>5/3 (Lemma 7). :contentReference[oaicite:3]{index=3}
*)
CONSTANTS
    GammaTotalShreds,
    GammaDataShreds

ASSUME
    /\ GammaTotalShreds \in Nat \ {0}
    /\ GammaDataShreds \in Nat \ {0}
    /\ GammaDataShreds < GammaTotalShreds
    /\ 3 * GammaTotalShreds > 5 * GammaDataShreds   \* κ = Γ/γ > 5/3 (Lemma 7). :contentReference[oaicite:4]{index=4}

(*
  StakeMap : Validator -> Nat and TotalStake are provided by Certificates.
  DeterministicBinCount implements PS‑P step 1: floor(ρ_i * Γ). (§3.1, Def. 46, step 1) :contentReference[oaicite:5]{index=5}
*)
DeterministicBinCount(v) ==
    (StakeMap[v] * GammaTotalShreds) \div TotalStake

(*
  Large stakeholders have at least one deterministic bin in step 1. (§3.1) :contentReference[oaicite:6]{index=6}
*)
LargeStakeholders(S) == { v \in S : DeterministicBinCount(v) >= 1 }

(*
  Total deterministic bins from step 1, capped at Γ. (§3.1, Def. 46, step 1) :contentReference[oaicite:7]{index=7}
*)
TotalDeterministicBinsExact(needers) ==
    LET large == LargeStakeholders(needers)
        SumDet[S \in SUBSET large] ==
            IF S = {} THEN 0
            ELSE LET v == CHOOSE x \in S : TRUE IN
                 DeterministicBinCount(v) + SumDet[S \ {v}]
        total == SumDet[large]
    IN IF total >= GammaTotalShreds THEN GammaTotalShreds ELSE total

(*
  Residual bins k and per‑validator residual stake units:
  After step 1, each v keeps residual ρ'_v = ρ_v − floor(ρ_v Γ)/Γ < 1/Γ (for all). (§3.1) :contentReference[oaicite:8]{index=8}
  We model this exactly with integers: units are multiples of TotalStake/Γ.
*)
ResidualBins(needers) ==
    LET d == TotalDeterministicBinsExact(needers)
    IN IF d >= GammaTotalShreds THEN {} ELSE (d + 1)..GammaTotalShreds

ResidualStakeUnits(v) ==
    StakeMap[v] * GammaTotalShreds - DeterministicBinCount(v) * TotalStake

ResidualEligible(needers) == { v \in needers : ResidualStakeUnits(v) > 0 }

(*
  Generic integer “sum of function over a set” helpers for partition checks.
*)
SumFunOverSet(fun, S) ==
  LET SumH[T \in SUBSET S] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE
             IN fun[x] + SumH[T \ {x}]
  IN SumH[S]

SumOverBinsForV(part, bins, v) ==
  LET SumH[T \in SUBSET bins] ==
        IF T = {} THEN 0
        ELSE LET j == CHOOSE y \in T : TRUE
             IN part[j][v] + SumH[T \ {j}]
  IN SumH[bins]

(*
  PSPPartitionOK captures Def. 46, step 2:
   - Partition residual stake across residual bins;
   - Each residual bin sums to exactly TotalStake units;
   - For each v, the total across bins equals its residual units.
  All entries are Nats, so no reals are needed. (§3.1, Def. 46) :contentReference[oaicite:9]{index=9}
*)
PSPPartitionOK(part, needers) ==
  LET bins == ResidualBins(needers)
      rem  == ResidualEligible(needers)
  IN /\ DOMAIN part = bins
     /\ \A j \in bins :
           /\ DOMAIN part[j] = rem
           /\ \A v \in rem : part[j][v] \in Nat
           /\ SumFunOverSet([ v \in rem |-> part[j][v] ], rem) = TotalStake
     /\ \A v \in rem :
           SumOverBinsForV(part, bins, v) = ResidualStakeUnits(v)

(*
  EligibleInBin per PS‑P step 3: positive mass means can be sampled. (§3.1) :contentReference[oaicite:10]{index=10}
*)
EligibleInBin(part, j) == { v \in DOMAIN part[j] : part[j][v] > 0 }

(*
  PSPConstraint enforces PS‑P:
   • Step 1: exact deterministic multiplicities for the first d bins.
   • Step 2+3: there exists a valid partition and each residual bin picks v with positive mass.
  This is a structural, non‑probabilistic abstraction of sampling. (§3.1) :contentReference[oaicite:11]{index=11}
*)
PSPConstraint(bins, needers) ==
  LET d   == TotalDeterministicBinsExact(needers)
      res == ResidualBins(needers)
      rem == ResidualEligible(needers)
  IN /\ DOMAIN bins = 1..GammaTotalShreds
     /\ \A v \in needers :
          Cardinality({ j \in 1..d : bins[j] = v }) = DeterministicBinCount(v)
     /\ \A j \in res : bins[j] \in rem

PSPConstraintExact(bins, needers) == PSPConstraint(bins, needers)
\* Kept for clarity; equality states no further approximation. (§3.1) :contentReference[oaicite:12]{index=12}

(*
  BinsToRelaySet collects the set of relays appearing in bins.
  Note multiplicities are in bins; the set is used only for selection output. (§2.2) :contentReference[oaicite:13]{index=13}
*)
BinsToRelaySet(bins) ==
    { bins[j] : j \in DOMAIN bins }

(*
  Rotor success (assignment-level): leader correct AND ≥ γ correct assignments.
  This matches Def. 6 precisely, counting assignments, not unique nodes. (§2.2) :contentReference[oaicite:14]{index=14}
*)
CorrectAssignmentsCount(bins, correctNodes) ==
    Cardinality({ j \in DOMAIN bins : bins[j] \in correctNodes })

RotorSuccessfulBins(leader, bins, correctNodes) ==
    /\ leader \in correctNodes
    /\ CorrectAssignmentsCount(bins, correctNodes) >= GammaDataShreds
\* See Def. 6 and Lemma 7 for resilience intuition with κ>5/3. :contentReference[oaicite:15]{index=15}

(*
  StructuralBinOK isolates the PS‑P constraint; no resilience guard here.
  Selection cannot depend on which nodes are correct. (§2.2 sampling vs. §2.9 safety) :contentReference[oaicite:16]{index=16}
*)
StructuralBinOK(bins, needers, nextLeader) ==
    PSPConstraintExact(bins, needers)

(*
  Candidate bin assignments are those structurally valid under PS‑P.
*)
BinCandidates(needers, nextLeader) ==
    { bins \in [1..GammaTotalShreds -> needers] :
        StructuralBinOK(bins, needers, nextLeader) }

(*
  PSPSelect chooses any candidate’s induced relay set.
  The protocol samples; the model allows any selection consistent with PS‑P. (§3.1) :contentReference[oaicite:17]{index=17}
*)
PSPSelect(needers, nextLeader) ==
    LET candBins == BinCandidates(needers, nextLeader)
        candSets == { BinsToRelaySet(b) : b \in candBins }
    IN IF candSets = {} THEN {} ELSE CHOOSE s \in candSets : TRUE

RotorBinAssignmentPossible(needers, nextLeader) ==
    IF needers = {} THEN TRUE ELSE BinCandidates(needers, nextLeader) # {}

(*
  RotorSelect:
   • Empty input yields empty set.
   • Fail closed if no PS‑P‑valid assignment exists.
   • Otherwise return any PS‑P‑consistent relay set.
  No stake-threshold gate; the paper has no such gate. (§2.2, §3.1) :contentReference[oaicite:18]{index=18}
*)
RotorSelect(block, needers, nextLeader) ==
    IF needers = {} THEN {}
    ELSE IF ~RotorBinAssignmentPossible(needers, nextLeader)
         THEN {}
         ELSE PSPSelect(needers, nextLeader)

(*
  Minor latency model hooks for “send shred to next leader first”. (§2.2) :contentReference[oaicite:19]{index=19}
*)
OnPath(nextLeader, relays) == nextLeader \in relays
NextDisseminationDelay(relays, nextLeader) == IF OnPath(nextLeader, relays) THEN 0 ELSE 1

(*
  Soundness lemma for the selector: any non-empty selection corresponds to
  some PS‑P‑valid bins that induce it. Resilience is evaluated separately via
  RotorSuccessfulBins with correctNodes. (§2.2, §2.9) :contentReference[oaicite:20]{index=20}
*)
RotorSelectSound(block, needers, nextLeader) ==
    LET sel == RotorSelect(block, needers, nextLeader)
    IN /\ (needers # {} /\ ~RotorBinAssignmentPossible(needers, nextLeader) => sel = {})
       /\ (sel # {} =>
            \E bins \in [1..GammaTotalShreds -> needers] :
                /\ StructuralBinOK(bins, needers, nextLeader)
                /\ BinsToRelaySet(bins) = sel)

=============================================================================
