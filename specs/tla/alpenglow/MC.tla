---------------------------- MODULE MC ----------------------------
(***************************************************************************
 * MODEL-CHECKING HARNESS
 *
 * Instantiates the abstract constants with a tiny network that still
 * exercises both fast (80%) and slow (60%) paths. Whitepaper §1.5 describes
 * the underlying model assumptions—partial synchrony, known validator set.
 ***************************************************************************)
EXTENDS MainProtocol, TLC

CONSTANTS v1, v2, v3, b0, b1, b2, b3, b4, b5, nullBlock

\* Stake distribution: validator v1 holds 60% stake, v2 holds 40%. With two
\* validators this lets TLC explore both the ≥80% fast path and ≥60% slow path.
MC_StakeMap == [v \in Validators |-> IF v = v1 THEN 60 ELSE 40]

\* Stake-weighted leader schedule constant for WindowSize = 2
MC_LeaderSchedule == [s \in Slots |-> IF s = 0 THEN v1 ELSE v2]

=============================================================================
