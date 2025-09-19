# Certificates.tla — Standards Compliance Report

**Scope**: specs/tla/alpenglow/Certificates.tla  
**EXTENDS**: Naturals, FiniteSets, Messages  
**Standards Source**: tla-docs.md (Standards Catalog loaded)

## 0) TL;DR
- Overall: Pass
- Correct sections: Module Header, CONSTANTS/ASSUME, Derived Operators/Helpers, Invariants
- Issues found: 0 Blocker / 0 Major / 0 Minor
- Top fixes: None required

## 1) Standards Catalog (from tla-docs.md)
- Top 10 MUST checklist: same as MainProtocol (STD-001…010). Key items: STD-001, STD-002, STD-007, STD-008.
- Full Catalog reference: See MainProtocol.tla.report.md.

## 2) Section-by-Section Analysis
### A. Module Header & EXTENDS (lines 1–13)
- Intent: Certificate generation and stake aggregation utilities.
- Standards Check: STD-001, STD-008 → Correct
- Evidence: specs/tla/alpenglow/Certificates.tla:1–13; tla-docs.md:52
- Patch: None
- Confidence: High
- Mini Summary: Proper header/imports.

### B. CONSTANTS / ASSUME (lines 19–24)
- Intent: StakeMap constant with positivity and total stake base.
- Standards Check: STD-002 → Correct
- Evidence: specs/tla/alpenglow/Certificates.tla:19–24; tla-docs.md:52, 885–887
- Patch: None
- Confidence: High
- Mini Summary: Constants are well-constrained.

### C. VARIABLES (Absent)
- Intent: N/A — data/utility module.
- Standards Check: STD-003 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: No state by design.

### D. State Predicates (TYPEOK, invariants) (lines 189–207, 231–251)
- Intent: IsValidCertificate and conflict/implication predicates; AllCertificatesValid and NoConflictingCertificates invariants.
- Standards Check: STD-007 → Correct
- Evidence: specs/tla/alpenglow/Certificates.tla:189–207,234–251; tla-docs.md:58, 106
- Patch: None
- Confidence: High
- Mini Summary: Invariants are explicit and reusable in higher specs.

### E. Init (Absent)
- Intent: N/A.
- Standards Check: STD-004 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: N/A.

### F. Next & Actions (incl. frame conditions) (Absent)
- Intent: N/A.
- Standards Check: STD-004, STD-005 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: N/A.

### G. Derived Operators / Helpers (lines 29–171, 145–184)
- Intent: Stake calculations (TotalStake, CalculateStake, UniqueValidators, StakeFromVotes), thresholds, can-create certificate predicates, and constructors.
- Standards Check: STD-008 → Correct
- Evidence: specs/tla/alpenglow/Certificates.tla:29–171,145–184; tla-docs.md:54
- Patch: None
- Confidence: High
- Mini Summary: Clean operator style and clear intent.

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
- Mini Summary: Used via MainProtocol invariants and MC.

### K. TLC/Config Mapping (if referenced)
- Intent: Imported into MainProtocol; used by MC.
- Standards Check: STD-010 → Correct
- Evidence: specs/tla/alpenglow/MC.cfg:2–63; tla-docs.md:144
- Patch: None
- Confidence: High
- Mini Summary: Indirect mapping through MainProtocol.

## 3) CTU Scorecard (vs Top 10 MUST)
| STD-### | Category | MUST/SHOULD | Status | Evidence |
|---------|----------|-------------|--------|----------|
| STD-001 | Structure | MUST | Pass | Certificates.tla:1–13 |
| STD-002 | Parameters | MUST | Pass | Certificates.tla:19–24 |
| STD-007 | Type invariant | SHOULD | Pass | 189–207,234–251 |
| STD-008 | Operator form | SHOULD | Pass | 29–171,145–184 |
| STD-009 | Prime discipline | MUST | Pass | N/A (no actions) |
| STD-010 | TLC mapping | SHOULD | Pass | MC.cfg:2–63 |

## 4) Issues & Minimal Patches
| ID | Section | Severity | Finding | Patch Ref | Evidence |
|----|---------|----------|---------|-----------|----------|
| — | — | — | No issues found | — | — |

## 5) Green Sections (Correct)
- Header & EXTENDS → [STD-001, STD-008].
- Constants/ASSUME → [STD-002].
- Stake/certificate helpers → [STD-008].
- Invariants → [STD-007].

## 6) Open Questions (if any)
- None.

## 7) Change Log
- Pass 1: Initial assessment. No changes required.

