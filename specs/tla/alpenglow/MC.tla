---------------------------- MODULE MC ----------------------------
(***************************************************************************
 * Model checking harness.
 * Provides minimal concrete parameters consistent with Whitepaper §1.5’s
 * model (small validator set, bounded slots) so TLC can explore behaviour.
 ***************************************************************************)
EXTENDS MainProtocol, TLC

CONSTANTS v1, v2, v3, b0, b1, b2, b3, b4, b5, nullBlock

\* Define concrete StakeMap function for model checking (60/40 stake split
\* exercises both the ≥80% fast path and ≥60% slow path thresholds.)
MC_StakeMap == [v \in Validators |-> IF v = v1 THEN 60 ELSE 40]

\* Stake-weighted leader schedule constant for WindowSize = 2
MC_LeaderSchedule == [s \in Slots |-> IF s = 0 THEN v1 ELSE v2]

=============================================================================
