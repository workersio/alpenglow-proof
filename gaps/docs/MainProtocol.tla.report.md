# MainProtocol.tla — Standards Compliance Report

**Scope**: specs/tla/alpenglow/MainProtocol.tla  
**EXTENDS**: Naturals, FiniteSets, Sequences, TLC, Messages, Blocks, Certificates, VoteStorage, VotorCore, Rotor  
**Standards Source**: tla-docs.md (Standards Catalog loaded)

## 0) TL;DR
- Overall: Pass
- Correct sections: Module Header, CONSTANTS/ASSUME, VARIABLES, Init, Next & Actions, Temporal Properties, Fairness, State Predicates, TLC/Config Mapping
- Issues found: 0 Blocker / 0 Major / 0 Minor
- Top fixes: None required

## 1) Standards Catalog (from tla-docs.md)
- Top 10 MUST checklist
  - STD-001 (Structure, MUST): “TLA+ specifications are organized in modules …” and use standard libraries via EXTENDS (tla-docs.md:52). Ensure proper module header and imports.
  - STD-002 (Parameters, MUST): Constants represent fixed entities; constrain them with ASSUME as needed (tla-docs.md:52, 885–887).
  - STD-003 (Variables, MUST): Variables represent state that changes during execution (tla-docs.md:52).
  - STD-004 (Spec Form, SHOULD): Standard form I ∧ □[N]_v ∧ L with disjunctive Next and fairness over disjuncts (tla-docs.md:76–84).
  - STD-005 (Frame/Stuttering, MUST): Use □[N]_v and UNCHANGED to define frame conditions; allow stuttering (tla-docs.md:82).
  - STD-006 (Fairness, SHOULD): Use WF_/SF_ to encode liveness assumptions on action disjuncts (tla-docs.md:84).
  - STD-007 (Type Invariant, SHOULD): Define TYPE/TypeInvariant and assert it; keep types explicit (tla-docs.md:58, 106).
  - STD-008 (Operator Form, SHOULD): Define operators as Op(args) == Expr (tla-docs.md:54).
  - STD-009 (Prime Discipline, MUST): Unprimed = pre-state, primed = post-state; only in actions (tla-docs.md:74).
  - STD-010 (TLC Mapping, SHOULD): Model config declares SPECIFICATION, INVARIANTS, PROPERTIES (tla-docs.md:144).
- Full Catalog reference
  - STD-001 — Module/EXTENDS (MUST). Quote: “TLA+ specifications are organized in modules … standard library …” (52). Rationale: enforce proper module scaffolding.
  - STD-002 — Constants & ASSUME (MUST). Quote: “Constant parameters represent entities whose values are fixed …” (52) and use ASSUME to constrain (885–887). Rationale: separate environment from behavior.
  - STD-003 — Variables (MUST). Quote: “variable parameters represent entities whose values change during system execution” (52). Rationale: explicit state.
  - STD-004 — Spec form I ∧ □[N]_v ∧ L (SHOULD). Quote: “While not mandatory, this is the standard form … L is a conjunction of fairness properties, each concerning a disjunct of the next-state relation.” (78–84). Rationale: clarity and tool support.
  - STD-005 — Stuttering/frame (MUST). Quote: “□[N]_v … admits ‘stuttering transitions’ …” (82). Rationale: refinement-friendly specs; require UNCHANGED in actions.
  - STD-006 — Fairness WF_/SF_ (SHOULD). Quote: “Fairness conditions complement … weak/strong fairness …” (84). Rationale: liveness assumptions.
  - STD-007 — Type invariant (SHOULD). Quote: “TypeInvariant states the intended ‘types’ … assert … towards the end …” (58, 106). Rationale: type clarity and model safety.
  - STD-008 — Operator definitions (SHOULD). Quote: “definitions in TLA+ take the form …” (54). Rationale: readable operators.
  - STD-009 — Prime discipline (MUST). Quote: “unprimed … before the transition … primed … successor state” (74). Rationale: sound action semantics.
  - STD-010 — TLC model mapping (SHOULD). Quote: “configuration file … SPECIFICATION … INVARIANTS … PROPERTIES” (144). Rationale: verifiable setup.
  - STD-011 — Vars tuple framing (SHOULD). Practice: define `vars` to list all VARIABLES used by [N]_vars (82). Rationale: explicit frame and stuttering.
  - STD-012 — Use standard library modules (MAY). Practice: EXTENDS FiniteSets/Naturals etc. (52). Rationale: reuse proven math library.
  - STD-013 — Fairness per disjunct (SHOULD). Quote: fairness “each concerning a disjunct of the next-state relation.” (82). Rationale: precise liveness.
  - STD-014 — Safety vs. Liveness separation (SHOULD). Quote: defines “The following section defines the two main correctness properties Safety and Liveness.” (86–88). Rationale: clarity and checkability.

## 2) Section-by-Section Analysis
### A. Module Header & EXTENDS (lines 1–17)
- Intent (plain English): Declares the protocol module and imports math/TLC and dependent submodules for messages, blocks, certificates, storage, Votor core, and Rotor.
- Standards Check: STD-001, STD-008 → Correct
- Evidence: specs/tla/alpenglow/MainProtocol.tla:1–17; tla-docs.md:52
- Patch (if needed): None
- Confidence: High
- Mini Summary: Proper module header and required EXTENDS are present.

### B. CONSTANTS / ASSUME (lines 22–36)
- Intent: Parameterize system size, Byzantine bound, GST, and bounding parameters for model checking; assert basic constraints (nonnegativity, < relation).
- Standards Check: STD-002 → Correct
- Evidence: specs/tla/alpenglow/MainProtocol.tla:22–36; tla-docs.md:52, 885–887
- Patch: None
- Confidence: High
- Mini Summary: Constants are clearly separated and constrained with ASSUME.

### C. VARIABLES (lines 41–50)
- Intent: Declare protocol state: per-validator state, block set, network messages, Byzantine set, time, finalized blocks, and per-node availability; aggregate in vars.
- Standards Check: STD-003, STD-005 → Correct
- Evidence: specs/tla/alpenglow/MainProtocol.tla:41–50; tla-docs.md:52, 82
- Patch: None
- Confidence: High
- Mini Summary: Variables are explicit and summarized in a vars tuple for framing.

### D. State Predicates (TYPEOK, invariants) (lines 592–619)
- Intent: TypeInvariant plus composite Invariant aggregating all safety properties and storage guarantees.
- Standards Check: STD-007 → Correct
- Evidence: specs/tla/alpenglow/MainProtocol.tla:592–619; tla-docs.md:58, 106
- Patch: None
- Confidence: High
- Mini Summary: Strong, explicit type and safety invariants are provided.

### E. Init (lines 87–101)
- Intent: Initialize validators (ready at slot 1 with Genesis as parent), blocks to {GenesisBlock}, clean network/state, Byzantine set by count, time zero, empty finalized, and full genesis availability.
- Standards Check: STD-004, STD-005 → Correct
- Evidence: specs/tla/alpenglow/MainProtocol.tla:87–101; tla-docs.md:76–84
- Patch: None
- Confidence: High
- Mini Summary: Clean initial condition consistent with data modules and genesis.

### F. Next & Actions (incl. frame conditions) (lines 102–239, 242–273, 290–333, 338–389, 394–413)
- Intent: Define all transition actions: receive/process block, timeouts, certificate generation, finalization, honest/Byzantine proposals, time advance, dissemination success/failure, repair, propagation, internal event emissions; Next is a disjunction of these.
- Standards Check: STD-004, STD-005, STD-006 → Correct
- Rationale: Actions consistently use primed updates and UNCHANGED for frame; Next is a clear disjunction; Fairness later targets action disjuncts; all primes appear only in actions.
- Evidence: specs/tla/alpenglow/MainProtocol.tla:102–239,242–273,290–333,338–389,394–413; tla-docs.md:74, 76–84
- Patch: None
- Confidence: High
- Mini Summary: Next is well-factored into actions with explicit frame conditions.

### G. Derived Operators / Helpers (lines 52–83, 56–83; helper block around 56–83 and 65–83, etc.)
- Intent: Define helper predicates/functions for correct nodes, rotor filtering, repair triggers, GST checks, stake checks.
- Standards Check: STD-008 → Correct
- Evidence: specs/tla/alpenglow/MainProtocol.tla:52–83; tla-docs.md:54
- Patch: None
- Confidence: High
- Mini Summary: Helpers follow standard operator definition style.

### H. Temporal Properties (Safety/Liveness) (lines 440–619)
- Intent: State safety invariants (chain, non-conflict, uniqueness) and liveness properties (eventual finalization, progress, window finalization premises).
- Standards Check: STD-004, STD-006, STD-014 → Correct
- Evidence: specs/tla/alpenglow/MainProtocol.tla:440–619; tla-docs.md:78–88
- Patch: None
- Confidence: High
- Mini Summary: Safety and liveness are clearly separated and precise.

### I. Fairness (WF_/SF_) (lines 418–437)
- Intent: Weak fairness on honest progress actions reflecting post-GST behavior.
- Standards Check: STD-006, STD-013 → Correct
- Evidence: specs/tla/alpenglow/MainProtocol.tla:418–437; tla-docs.md:84
- Patch: None
- Confidence: High
- Mini Summary: Fairness covers honest actions; failure/Byzantine steps not forced.

### J. Theorems/Lemmas (no runs) (Absent)
- Intent: No THEOREM statements; properties are used via TLC config.
- Standards Check: STD-007 → Correct (via TLC invariants rather than THEOREM)
- Evidence: Absent explicitly; see config mapping.
- Patch: None
- Confidence: Medium
- Mini Summary: Using TLC invariants instead of THEOREM is acceptable for model checking.

### K. TLC/Config Mapping (if referenced) (MC.cfg, MC.tla)
- Intent: Model binds SPECIFICATION Spec; lists invariants and liveness properties; assigns constants and model values.
- Standards Check: STD-010 → Correct
- Evidence: specs/tla/alpenglow/MC.cfg:2–63; tla-docs.md:144
- Patch: None
- Confidence: High
- Mini Summary: Clean mapping from module formulas to TLC configuration.

## 3) CTU Scorecard (vs Top 10 MUST)
| STD-### | Category | MUST/SHOULD | Status | Evidence |
|---------|----------|-------------|--------|----------|
| STD-001 | Structure | MUST | Pass | MainProtocol.tla:1–17 |
| STD-002 | Parameters | MUST | Pass | MainProtocol.tla:22–36 |
| STD-003 | Variables | MUST | Pass | MainProtocol.tla:41–50 |
| STD-004 | Spec Form | SHOULD | Pass | MainProtocol.tla:438–439 |
| STD-005 | Frame/Stuttering | MUST | Pass | Actions use UNCHANGED; 82 |
| STD-006 | Fairness | SHOULD | Pass | MainProtocol.tla:418–437 |
| STD-007 | Type invariant | SHOULD | Pass | MainProtocol.tla:592–600 |
| STD-008 | Operator form | SHOULD | Pass | Various helpers (52–83) |
| STD-009 | Prime discipline | MUST | Pass | Actions (e.g., 110–116, 121–129) |
| STD-010 | TLC mapping | SHOULD | Pass | MC.cfg:2–63 |

## 4) Issues & Minimal Patches
| ID | Section | Severity | Finding | Patch Ref | Evidence |
|----|---------|----------|---------|-----------|----------|
| — | — | — | No issues found | — | — |

## 5) Green Sections (Correct)
- Header & EXTENDS → [STD-001, STD-008] — Proper module and imports.
- Constants/ASSUME → [STD-002] — Clear parameterization and assumptions.
- Variables → [STD-003, STD-005] — Explicit state, framed via vars.
- Init → [STD-004] — Genesis-centered initialization.
- Next & Actions → [STD-004, STD-005] — Disjunctive actions with UNCHANGED.
- Temporal Properties → [STD-014] — Clear safety/liveness separation.
- Fairness → [STD-006, STD-013] — WF_ on honest progress actions.
- TLC Mapping → [STD-010] — Spec/invariants/properties wired in MC.cfg.

## 6) Open Questions (if any)
- None. All constructs map clearly to the standards and are well-typed.

## 7) Change Log
- Pass 1: Initial assessment. No changes required.
