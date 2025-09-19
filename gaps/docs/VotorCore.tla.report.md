# VotorCore.tla — Standards Compliance Report

**Scope**: specs/tla/alpenglow/VotorCore.tla  
**EXTENDS**: Naturals, FiniteSets, Sequences, TLC, Messages, Blocks, Certificates, VoteStorage  
**Standards Source**: tla-docs.md (Standards Catalog loaded)

## 0) TL;DR
- Overall: Pass
- Correct sections: Module Header, Derived Operators/Helpers (validator state, TryNotar/TryFinal/Skip/Timeout handlers), Type Invariant
- Issues found: 0 Blocker / 0 Major / 0 Minor
- Top fixes: None required

## 1) Standards Catalog (from tla-docs.md)
- Top 10 MUST checklist: same as MainProtocol (STD-001…010). Key items: STD-001, STD-007, STD-008, STD-009.
- Full Catalog reference: See MainProtocol.tla.report.md.

## 2) Section-by-Section Analysis
### A. Module Header & EXTENDS (lines 1–17)
- Intent: Local validator voting logic and state machinery used by MainProtocol.
- Standards Check: STD-001, STD-008 → Correct
- Evidence: specs/tla/alpenglow/VotorCore.tla:1–17; tla-docs.md:52
- Patch: None
- Confidence: High
- Mini Summary: Proper header and imports.

### B. CONSTANTS / ASSUME (lines 18–25)
- Intent: Timing parameters DeltaTimeout/DeltaBlock with positivity constraints.
- Standards Check: STD-002 → Correct
- Evidence: specs/tla/alpenglow/VotorCore.tla:18–25; tla-docs.md:52, 885–887
- Patch: None
- Confidence: High
- Mini Summary: Clear assumptions.

### C. VARIABLES (Absent)
- Intent: Stateless operators over explicit ValidatorState values.
- Standards Check: STD-003 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: N/A.

### D. State Predicates (TYPEOK, invariants) (lines 317–327)
- Intent: ValidatorStateOK typing predicate.
- Standards Check: STD-007 → Correct
- Evidence: specs/tla/alpenglow/VotorCore.tla:317–327; tla-docs.md:58, 106
- Patch: None
- Confidence: High
- Mini Summary: Strong typing over local state.

### E. Init (lines 63–72)
- Intent: InitValidatorState constructor for an initial per-validator state.
- Standards Check: STD-004 → Correct (as a constructor)
- Evidence: specs/tla/alpenglow/VotorCore.tla:63–72
- Patch: None
- Confidence: High
- Mini Summary: Clean initialization operator.

### F. Next & Actions (incl. frame conditions) (lines 94–315)
- Intent: Pure-state transformation operators for voting and event handling (TryNotar, TryFinal, TrySkipWindow, CheckPendingBlocks, handlers for Block/Timeout/ParentReady/SafeTo*; clock advance function).
- Standards Check: STD-008, STD-009 → Correct
- Evidence: specs/tla/alpenglow/VotorCore.tla:94–315; tla-docs.md:54, 74
- Patch: None
- Confidence: High
- Mini Summary: Operators use EXCEPT updates; primes appear only where actions would use them in MainProtocol.

### G. Derived Operators / Helpers (lines 40–91)
- Intent: StateObject set; HasState/AddState; VotedForBlock helper.
- Standards Check: STD-008 → Correct
- Evidence: specs/tla/alpenglow/VotorCore.tla:40–91; tla-docs.md:54
- Patch: None
- Confidence: High
- Mini Summary: Helper operators are idiomatic and clear.

### H. Temporal Properties (Absent)
- Intent: N/A.
- Standards Check: STD-014 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: N/A.

### I. Fairness (WF_/SF_) (Absent)
- Intent: N/A.
- Standards Check: STD-006 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: N/A.

### J. Theorems/Lemmas (no runs) (Absent)
- Intent: N/A.
- Standards Check: STD-007 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: Medium
- Mini Summary: Verified through MainProtocol invariants and MC.

### K. TLC/Config Mapping (if referenced)
- Intent: Utilized through MainProtocol.
- Standards Check: STD-010 → Correct
- Evidence: specs/tla/alpenglow/MC.cfg:2–63
- Patch: None
- Confidence: High
- Mini Summary: Indirect mapping via MainProtocol.

## 3) CTU Scorecard (vs Top 10 MUST)
| STD-### | Category | MUST/SHOULD | Status | Evidence |
|---------|----------|-------------|--------|----------|
| STD-001 | Structure | MUST | Pass | VotorCore.tla:1–17 |
| STD-002 | Parameters | MUST | Pass | VotorCore.tla:18–25 |
| STD-007 | Type invariant | SHOULD | Pass | 317–327 |
| STD-008 | Operator form | SHOULD | Pass | 40–315 |
| STD-009 | Prime discipline | MUST | Pass | No primes in module actions; used in MainProtocol |
| STD-010 | TLC mapping | SHOULD | Pass | MC.cfg:2–63 |

## 4) Issues & Minimal Patches
| ID | Section | Severity | Finding | Patch Ref | Evidence |
|----|---------|----------|---------|-----------|----------|
| — | — | — | No issues found | — | — |

## 5) Green Sections (Correct)
- Header & EXTENDS → [STD-001, STD-008].
- Constants/ASSUME → [STD-002].
- Validator state/helpers → [STD-008].
- ValidatorStateOK → [STD-007].

## 6) Open Questions (if any)
- None.

## 7) Change Log
- Pass 1: Initial assessment. No changes required.

