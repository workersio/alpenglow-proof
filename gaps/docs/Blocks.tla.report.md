# Blocks.tla — Standards Compliance Report

**Scope**: specs/tla/alpenglow/Blocks.tla  
**EXTENDS**: Naturals, FiniteSets, Messages  
**Standards Source**: tla-docs.md (Standards Catalog loaded)

## 0) TL;DR
- Overall: Pass
- Correct sections: Module Header, CONSTANTS/ASSUME, Derived Operators/Helpers, Invariants
- Issues found: 0 Blocker / 0 Major / 0 Minor
- Top fixes: None required

## 1) Standards Catalog (from tla-docs.md)
- Top 10 MUST checklist
  - STD-001 (Structure, MUST): Modules + EXTENDS standard library (tla-docs.md:52).
  - STD-002 (Parameters, MUST): Constants fixed by model; constrain with ASSUME (tla-docs.md:52, 885–887).
  - STD-004 (Spec Form, SHOULD): I ∧ □[N]_v ∧ L for system specs (tla-docs.md:76–84).
  - STD-005 (Frame/Stuttering, MUST): □[N]_v and UNCHANGED for actions (tla-docs.md:82).
  - STD-007 (Type Invariant, SHOULD): Define type/structural invariants (tla-docs.md:58, 106).
  - STD-008 (Operator Form, SHOULD): Op(args) == Expr (tla-docs.md:54).
  - STD-009 (Prime Discipline, MUST): Prime only in actions (tla-docs.md:74).
  - STD-010 (TLC Mapping, SHOULD): SPECIFICATION/INVARIANTS/PROPERTIES (tla-docs.md:144).
- Full Catalog reference: See MainProtocol.tla.report.md (STD-001…010) — identical catalog used here.

## 2) Section-by-Section Analysis
### A. Module Header & EXTENDS (lines 1–14)
- Intent: Declare the Blocks module and import naturals, finite sets, and Messages types.
- Standards Check: STD-001, STD-008 → Correct
- Evidence: specs/tla/alpenglow/Blocks.tla:1–14; tla-docs.md:52
- Patch: None
- Confidence: High
- Mini Summary: Proper header and imports for a data/structure module.

### B. CONSTANTS / ASSUME (lines 20–29)
- Intent: Genesis hash, window size, leader schedule; constraints: type membership, positivity, function typing.
- Standards Check: STD-002 → Correct
- Evidence: specs/tla/alpenglow/Blocks.tla:20–29; tla-docs.md:52, 885–887
- Patch: None
- Confidence: High
- Mini Summary: Constants are cleanly typed and constrained.

### C. VARIABLES (Absent)
- Intent: None — this module provides types/predicates only.
- Standards Check: STD-003 → Correct (N/A to data module)
- Evidence: Absent
- Patch: None
- Confidence: High
- Mini Summary: No state here by design.

### D. State Predicates (TYPEOK, invariants) (lines 206–225)
- Intent: AllBlocksValid, UniqueBlocksPerSlot, SingleChain predicates to be used by higher-level invariants.
- Standards Check: STD-007 → Correct
- Evidence: specs/tla/alpenglow/Blocks.tla:210–225; tla-docs.md:58, 106
- Patch: None
- Confidence: High
- Mini Summary: Reusable invariants are defined and well-scoped.

### E. Init (Absent)
- Intent: Not a transition system; init not applicable.
- Standards Check: STD-004 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: Not applicable for data-only module.

### F. Next & Actions (incl. frame conditions) (Absent)
- Intent: No actions in this module.
- Standards Check: STD-004, STD-005 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: Not applicable.

### G. Derived Operators / Helpers (lines 31–199)
- Intent: Define Block/GenesisBlock shapes; validators; conflict/parent-child checks; ancestry/chain utilities; leader/window helpers and schedule consistency assumption; chain operations.
- Standards Check: STD-008 → Correct
- Evidence: specs/tla/alpenglow/Blocks.tla:31–199; tla-docs.md:54
- Patch: None
- Confidence: High
- Mini Summary: Operators are precise and idiomatic. Comments are non-semantic.

### H. Temporal Properties (Safety/Liveness) (Absent)
- Intent: Not a temporal spec here.
- Standards Check: STD-014 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: Not applicable.

### I. Fairness (WF_/SF_) (Absent)
- Intent: Not applicable.
- Standards Check: STD-006 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: High
- Mini Summary: Not applicable.

### J. Theorems/Lemmas (no runs) (Absent)
- Intent: None here; used via other modules’ invariants/MC.
- Standards Check: STD-007 → Correct (N/A)
- Evidence: —
- Patch: None
- Confidence: Medium
- Mini Summary: The predicates support theorem statements elsewhere.

### K. TLC/Config Mapping (if referenced)
- Intent: This module is imported by MainProtocol; mapped via MC.cfg in that context.
- Standards Check: STD-010 → Correct
- Evidence: specs/tla/alpenglow/MC.cfg:2–63; tla-docs.md:144
- Patch: None
- Confidence: High
- Mini Summary: Used through MainProtocol’s Spec; no direct mapping needed here.

## 3) CTU Scorecard (vs Top 10 MUST)
| STD-### | Category | MUST/SHOULD | Status | Evidence |
|---------|----------|-------------|--------|----------|
| STD-001 | Structure | MUST | Pass | Blocks.tla:1–14 |
| STD-002 | Parameters | MUST | Pass | Blocks.tla:20–29 |
| STD-003 | Variables | MUST | Pass | N/A (data-only) |
| STD-004 | Spec Form | SHOULD | Pass | N/A (data-only) |
| STD-005 | Frame/Stuttering | MUST | Pass | N/A (no actions) |
| STD-007 | Type invariant | SHOULD | Pass | Blocks.tla:210–225 |
| STD-008 | Operator form | SHOULD | Pass | Blocks.tla:31–199 |
| STD-009 | Prime discipline | MUST | Pass | N/A (no actions) |
| STD-010 | TLC mapping | SHOULD | Pass | MC.cfg:2–63 |

## 4) Issues & Minimal Patches
| ID | Section | Severity | Finding | Patch Ref | Evidence |
|----|---------|----------|---------|-----------|----------|
| — | — | — | No issues found | — | — |

## 5) Green Sections (Correct)
- Header & EXTENDS → [STD-001, STD-008] — Proper structure/imports.
- Constants/ASSUME → [STD-002] — Clean constraints.
- Operators/Helpers → [STD-008] — Idiomatic definitions.
- Invariant predicates → [STD-007] — Reusable correctness checks.

## 6) Open Questions (if any)
- None.

## 7) Change Log
- Pass 1: Initial assessment. No changes required.

