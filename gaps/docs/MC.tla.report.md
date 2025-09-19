# MC.tla — Standards Compliance Report

**Scope**: specs/tla/alpenglow/MC.tla  
**EXTENDS**: MainProtocol, TLC  
**Standards Source**: tla-docs.md (Standards Catalog loaded)

## 0) TL;DR
- Overall: Pass
- Correct sections: Module Header, Derived Operators/Helpers (model values), TLC/Config Mapping
- Issues found: 0 Blocker / 0 Major / 0 Minor
- Top fixes: None required

## 1) Standards Catalog (from tla-docs.md)
- Top 10 MUST checklist: same as MainProtocol (STD-001…010). Key items: STD-001, STD-010.
- Full Catalog reference: See MainProtocol.tla.report.md.

## 2) Section-by-Section Analysis
### A. Module Header & EXTENDS (lines 1–9)
- Intent: MC harness extending MainProtocol for tiny model instantiation.
- Standards Check: STD-001 → Correct
- Evidence: specs/tla/alpenglow/MC.tla:1–9; tla-docs.md:52
- Patch: None
- Confidence: High
- Mini Summary: Proper harness module.

### B. CONSTANTS / ASSUME (lines 11–19)
- Intent: Model values for validators and block hashes; helper functions MC_StakeMap and MC_LeaderSchedule.
- Standards Check: STD-002, STD-008 → Correct
- Evidence: specs/tla/alpenglow/MC.tla:11–19; tla-docs.md:54
- Patch: None
- Confidence: High
- Mini Summary: Clean, deterministic model bindings.

### C. VARIABLES (Absent)
- Intent: N/A (harness only).
- Standards Check: STD-003 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: N/A.

### D. State Predicates (TYPEOK, invariants) (Absent)
- Intent: N/A.
- Standards Check: STD-007 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: N/A.

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

### G. Derived Operators / Helpers (lines 13–19)
- Intent: Provide small stake distribution and leader schedule used by MC.cfg via “<-” bindings.
- Standards Check: STD-008 → Correct
- Evidence: specs/tla/alpenglow/MC.tla:13–19; tla-docs.md:54
- Patch: None
- Confidence: High
- Mini Summary: Helper defs are simple and well-scoped.

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
- Mini Summary: N/A.

### K. TLC/Config Mapping (if referenced)
- Intent: Bound via MC.cfg using SPECIFICATION/INVARIANTS/PROPERTIES.
- Standards Check: STD-010 → Correct
- Evidence: specs/tla/alpenglow/MC.cfg:2–63; tla-docs.md:144
- Patch: None
- Confidence: High
- Mini Summary: Proper model mapping to module formulas.

## 3) CTU Scorecard (vs Top 10 MUST)
| STD-### | Category | MUST/SHOULD | Status | Evidence |
|---------|----------|-------------|--------|----------|
| STD-001 | Structure | MUST | Pass | MC.tla:1–9 |
| STD-008 | Operator form | SHOULD | Pass | 13–19 |
| STD-010 | TLC mapping | SHOULD | Pass | MC.cfg:2–63 |

## 4) Issues & Minimal Patches
| ID | Section | Severity | Finding | Patch Ref | Evidence |
|----|---------|----------|---------|-----------|----------|
| — | — | — | No issues found | — | — |

## 5) Green Sections (Correct)
- Header & EXTENDS → [STD-001].
- Model helpers → [STD-008].
- TLC mapping → [STD-010].

## 6) Open Questions (if any)
- None.

## 7) Change Log
- Pass 1: Initial assessment. No changes required.

