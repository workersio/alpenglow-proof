# Alpenglow TLA+ Specification - Issues and Ambiguities

**Verification Date:** 2025-09-29  
**Verifier:** Claude (Formal Verification Specialist)  
**Whitepaper Version:** v1.1, July 22, 2025  

---

## Executive Summary

This document identifies issues, ambiguities, and areas requiring clarification in the Alpenglow TLA+ specification relative to the whitepaper. The specification is **generally well-aligned** with the whitepaper and demonstrates high-quality formal modeling. However, several areas require attention or clarification.

**Overall Assessment:** ✅ Strong alignment with whitepaper; minor clarifications needed

---

## Critical Issues

### None Identified

No critical safety or liveness violations were found in the specification that contradict the whitepaper claims.

---

## Moderate Issues

### 1. Rotor Bin Assignment Multiplicity Semantics

**Location:** `Rotor.tla:160-170` (PSPConstraint)  
**Whitepaper Reference:** §3.1, Definition 46 (:1154)

**Issue:**
The PSPConstraint enforces that `Cardinality({ j : bins[j] = v }) >= DeterministicBinCount(v)`, which is a **lower bound** on multiplicities. However, the whitepaper's PS-P sampling (Definition 46) suggests **exact** multiplicities for Step 1:
- Step 1 should assign **exactly** `⌊ρᵥ·Γ⌋` bins to each large stakeholder `v`
- The current spec allows over-assignment in the deterministic prefix

**Impact:** Moderate - affects modeling accuracy of relay sampling but does not violate safety.

**Recommendation:**
Consider strengthening PSPConstraint to enforce exact multiplicities for bins `1..TotalDeterministicBinsExact(needers)`, or add a clarifying comment explaining why the lower bound suffices for the abstraction level chosen.

---

### 2. Rotor Success Definition Discrepancy

**Location:** `Rotor.tla:244-247` (RotorSuccessful vs RotorSuccessfulBins)  
**Whitepaper Reference:** §2.2, Definition 6 (:414)

**Issue:**
Two success predicates are provided:
1. `RotorSuccessful`: counts **distinct** relays (set-based)
2. `RotorSuccessfulBins`: counts **by-bin** assignments (multiplicity-aware)

The whitepaper's Definition 6 states "at least γ correct relays," which could be interpreted either way. The specification uses `RotorSuccessfulBins` in MainProtocol but provides both.

**Ambiguity:**
Does "at least γ correct relays" mean:
- γ distinct correct validators selected as relays? OR
- γ bin assignments to correct validators (allowing multiplicity)?

**Impact:** Moderate - affects which configurations satisfy Rotor success.

**Recommendation:**
Clarify in the specification comments which interpretation aligns with the whitepaper authors' intent, or state that both are valid abstractions at different levels.

---

### 3. SafeToNotar/SafeToSkip Event Re-emission

**Location:** `MainProtocol.tla:657,687` (EmitSafeToNotar, EmitSafeToSkip)  
**Whitepaper Reference:** §2.5, Definition 16 (:554, :571)

**Issue:**
The guards use `~HasState(validator, s, "BadWindow")` to prevent re-emission after a fallback vote is cast. However, the whitepaper's Algorithm 1 (lines ~16-25) does not explicitly specify re-emission suppression beyond the "already voted" preconditions.

**Ambiguity:**
Is it valid to emit SafeToNotar/SafeToSkip multiple times if the inequality continues to hold, or is it intended to be emitted at most once per slot?

**Current Behavior:** The spec suppresses re-emission via BadWindow flag.

**Impact:** Minor - affects event emission count but not safety.

**Recommendation:**
Add a comment in the whitepaper or spec clarifying the intended emission cardinality per slot/validator.

---

## Minor Issues and Observations

### 4. Genesis Block Representation

**Location:** `Blocks.tla:60-68` (GenesisBlock)  
**Whitepaper Reference:** §2.1, implicit

**Observation:**
The specification models genesis as slot 0, self-parented (`parent = GenesisHash`). The whitepaper does not prescribe a specific genesis representation, only reasoning "from genesis."

**Status:** Acceptable modeling choice; well-documented in comments.

**Recommendation:** None; current approach is sound.

---

### 5. Timeout Schedule Formula Clarity

**Location:** `VotorCore.tla:339` (HandleParentReady timeout calculation)  
**Whitepaper Reference:** §2.6, Definition 17 (:609)

**Observation:**
The timeout formula is:
```tla
timeout == val.clock + DeltaTimeout + ((s - first + 1) * DeltaBlock)
```

This matches Definition 17's `Δ_timeout + (i - s + 1)·Δ_block` where `i` is the slot and `s` is the first slot of the window. However, the variable naming (`s` for current slot, `first` for window start) reverses the roles compared to the paper's notation.

**Status:** Correct formula; notation differs from paper.

**Recommendation:** Consider renaming for clarity (e.g., `slot` instead of `s`, `windowStart` instead of `first`) or add an explicit mapping comment.

---

### 6. Repair Trigger Completeness

**Location:** `MainProtocol.tla:138-143` (NeedsBlockRepair)  
**Whitepaper Reference:** §2.8, Algorithm 4 (:801)

**Observation:**
The repair trigger checks for:
- FastFinalizationCert
- NotarizationCert
- NotarFallbackCert

The whitepaper's Algorithm 4 and Definition 15 suggest repair is needed when certificates imply a block should exist. The current trigger seems appropriate but could be more explicit about triggering on **any** certificate that references a block hash (including finalization certs in principle, though those are slot-scoped).

**Status:** Reasonable abstraction; may under-trigger in edge cases.

**Recommendation:** Consider adding a comment clarifying the repair trigger philosophy or confirming that the current set is complete.

---

### 7. BlockNotarized Event Hash Binding

**Location:** `VotorCore.tla:138-142` (BlockNotarizedHashes)  
**Whitepaper Reference:** §2.5, Definition 15 (:543)

**Observation:**
The specification models `BlockNotarized` as an unparameterized state flag, with the hash carried via Pool certificates. The whitepaper writes `BlockNotarized(hash(b))` as a parameterized event.

**Status:** Acceptable modeling choice; well-explained in comments (VotorCore.tla:44-76).

**Recommendation:** None; the split representation is a sound abstraction.

---

### 8. Fast Path Latency Parameter Naming

**Location:** `MainProtocol.tla:52-53` (Delta80, Delta60)  
**Whitepaper Reference:** §1.3, §1.5 (:241)

**Observation:**
The whitepaper uses `δ_θ` notation (e.g., δ₈₀%, δ₆₀%) to denote network delay for a stake-weighted fraction θ. The spec uses `Delta80` and `Delta60` as model parameters.

**Clarification Needed:**
Are Delta80 and Delta60 meant to model:
1. The **network propagation delay** to θ% stake? OR
2. The **total time bound** for finalization (including vote aggregation)?

The BoundedFinalization invariants treat them as time budgets, which aligns with the whitepaper's intent of `min(δ₈₀%, 2δ₆₀%)` finalization time.

**Status:** Likely correct but could be clearer.

**Recommendation:** Add a comment clarifying that Delta80/Delta60 model the network delay components in the finalization time formula.

---

### 9. SkipCert vs BlockCert Mutual Exclusion Enforcement

**Location:** `VoteStorage.tla:158` (CanStoreCertificate), `Certificates.tla:341-345` (SkipVsBlockCertExclusion)  
**Whitepaper Reference:** §2.6, implicit from Algorithm 1-2

**Observation:**
The specification explicitly enforces mutual exclusion between SkipCert and block-related certificates (NotarizationCert, NotarFallbackCert, FastFinalizationCert) at the Pool storage level.

The whitepaper does not state this as an explicit invariant but implies it through the voting logic (a node votes either to notarize a block OR to skip the slot, never both).

**Status:** Reasonable strengthening; consistent with protocol intent.

**Recommendation:** Confirm this is an intended invariant or clarify if concurrent skip/notar certs could theoretically coexist under adversarial scenarios.

---

### 10. Notarization Cert Uniqueness Across Fallback Levels

**Location:** `VoteStorage.tla:167-169` (CanStoreCertificate)  
**Whitepaper Reference:** §2.5, Definition 13 (:520)

**Observation:**
The storage rule enforces that all notar-family certs (NotarizationCert, NotarFallbackCert, FastFinalizationCert) in a slot must agree on the same `blockHash`:
```tla
/\ (\A c \in existing : c.type \in NotarTypes => c.blockHash = cert.blockHash)
```

This is stricter than the whitepaper's "single certificate of each type per block/slot" phrasing. However, it aligns with the safety intuition that only one block per slot can be notarized.

**Status:** Acceptable strengthening; consistent with Lemma 24 (:855).

**Recommendation:** None; this is a sound invariant.

---

## Ambiguities Requiring Whitepaper Clarification

### 11. Concurrent Processing of Multiple Slots

**Location:** `MainProtocol.tla` (overall protocol structure)  
**Whitepaper Reference:** §1.1 (:170), §2.7 (:678)

**Ambiguity:**
The whitepaper mentions "concurrent processing of slots allows block times to be shorter than the assumed latency bound (Δ)" (:170). The TLA+ spec allows multiple slots to be proposed and voted on concurrently (Next state relation is nondeterministic).

**Question:**
Does the whitepaper intend for:
1. **Pipelined slot processing:** Leaders can propose slot `i+1` before slot `i` is finalized?
2. **Window-level concurrency:** The leader processes all slots in its window concurrently?
3. **Something else?**

**Current Spec Behavior:** The spec allows pipelining (leaders can propose new blocks before prior blocks are finalized).

**Recommendation:** Clarify the concurrency model in the whitepaper or confirm that the spec's interpretation is correct.

---

### 12. Repair Triggering Timing

**Location:** `MainProtocol.tla:539-547` (RepairBlock)  
**Whitepaper Reference:** §2.8, Algorithm 4 (:801)

**Ambiguity:**
Algorithm 4 states "upon receiving a notarization certificate or an ancestor of a notarization certificate." The spec triggers repair when `NeedsBlockRepair` holds (certificate present but block missing).

**Question:**
Is repair:
1. **Reactive:** Triggered when a certificate arrives but the block is missing? OR
2. **Proactive:** Periodically retry fetching all missing certified blocks?

**Current Spec Behavior:** Reactive (checked via Next state relation).

**Recommendation:** Confirm that the reactive model aligns with the whitepaper's intent, or add proactive retry logic if needed.

---

### 13. FinalVote Issuance Without BadWindow Check

**Location:** `VotorCore.tla:164-177` (TryFinal)  
**Whitepaper Reference:** Algorithm 2, lines 18-21 (:847-849)

**Observation:**
TryFinal checks `~HasState(validator, slot, "BadWindow")` to prevent finalization voting in slots where fallback activity occurred. The whitepaper's Algorithm 2 line 20 has this check.

**Ambiguity:**
What is the rationale for preventing FinalVote in BadWindow slots? Is it:
1. **Safety:** Mixing finalization with fallback could violate invariants? OR
2. **Liveness:** Avoid conflicting vote types that could deadlock certificate formation?

**Current Spec Behavior:** Enforces mutual exclusion via Lemma22.

**Recommendation:** Add a comment in the whitepaper or spec explaining the BadWindow guard's purpose.

---

## Documentation Gaps

### 14. Missing Explicit Mapping for Lemmas

**Observation:**
The specification includes invariants for many whitepaper lemmas (e.g., Lemma 20, 24, 25) but not all lemmas from §2.9-§2.10 are explicitly named in the spec.

**Examples:**
- Lemma 21 (Fast-finalization prevents conflicting notarizations) - implied by SafetyInvariant but not separately stated
- Lemma 23 (> 40% correct stake prevents conflicting notarizations) - not directly stated as an invariant
- Lemma 26 (Slow-finalization prevents conflicting notarizations) - implied by SafetyInvariant

**Recommendation:**
Add explicit TLA+ predicates for all lemmas stated in the whitepaper, even if they are subsumed by higher-level invariants. This aids auditability and traceability.

---

### 15. Assumption 2 (Extra Crash Tolerance) Modeling

**Observation:**
The spec defines `UnresponsiveStakeOK` and mentions Assumption 2 (:121) in comments, but there's no separate invariant or property explicitly labeled "Assumption 2 Verification."

**Current Coverage:**
- Byzantine stake < 20%: ✅ Enforced in Invariant
- Unresponsive stake ≤ 20%: ✅ Enforced in Invariant
- Correct nodes > 60%: ✅ Implied by above

**Recommendation:**
Add an explicit `Assumption2OK` predicate combining the above checks, and reference it in liveness properties that rely on the extended crash tolerance model.

---

## Positive Observations

### Strengths of the Specification

1. **Comprehensive Coverage:** All major protocol components (Messages, Blocks, Certificates, VoteStorage, Rotor, VotorCore, MainProtocol) are modeled.

2. **Whitepaper Traceability:** Extensive line-by-line comments referencing specific whitepaper sections and line numbers (e.g., `:513`, `:820`).

3. **Well-Documented Abstractions:** Modeling choices (e.g., genesis self-parenting, BlockNotarized hash binding) are clearly explained.

4. **Safety Invariants:** Strong coverage of safety properties including:
   - SafetyInvariant (Theorem 1)
   - NoConflictingFinalization
   - VoteUniqueness (Lemma 20)
   - UniqueNotarization (Lemma 24)
   - FinalizedImpliesNotarized (Lemma 25)

5. **Liveness Properties:** Temporal properties for BasicLiveness, FastPathOneRound, Progress, and WindowFinalizationAll.

6. **Bounded-Time Finalization:** Novel ghost timers (`avail80Start`, `avail60Start`) and invariants (BoundedFinalization80, BoundedFinalization60) to model the `min(δ₈₀%, 2δ₆₀%)` finalization time claim.

7. **Rotor Modeling:** Detailed PS-P sampling abstraction with bin multiplicities, resilience constraints, and success predicates.

---

## Recommendations for Future Work

1. **Add Missing Lemma Predicates:** Create explicit TLA+ invariants for Lemmas 21, 23, 26, and other whitepaper lemmas not currently named in the spec.

2. **Clarify Rotor Success Semantics:** Choose one canonical success predicate (set-based or bin-based) or document when each applies.

3. **Strengthen PSPConstraint:** Consider enforcing exact multiplicities for deterministic bins if that matches the whitepaper's intent.

4. **Add Assumption 2 Predicate:** Create a named predicate grouping all Assumption 2 requirements for clarity.

5. **Cross-Reference All Theorems:** Ensure every theorem from §2.9-§2.11 has a corresponding TLA+ property or invariant.

6. **Model Checking Results:** Include a summary of TLC model checking results (e.g., state space explored, invariant violations, temporal property satisfaction) in the documentation.

7. **Proof Sketches:** Consider adding TLAPS (TLA+ Proof System) proof obligations for key safety lemmas to machine-check the proofs.

---

## Summary Statistics

- **Total Specification Files Reviewed:** 8 (Messages, Blocks, Certificates, VoteStorage, Rotor, VotorCore, MainProtocol, MC)
- **Whitepaper Sections Covered:** §1.1-§3.7 (full protocol)
- **Critical Issues:** 0
- **Moderate Issues:** 3
- **Minor Issues/Observations:** 10
- **Ambiguities:** 3
- **Documentation Gaps:** 2

---

## Conclusion

The Alpenglow TLA+ specification is **high-quality and well-aligned** with the whitepaper. The identified issues are mostly minor clarifications or documentation enhancements. No fundamental safety violations or critical misalignments were found. The specification is suitable for formal verification and can serve as a rigorous reference implementation of the protocol.

**Verification Confidence:** High ✅
