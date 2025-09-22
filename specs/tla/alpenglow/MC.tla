---------------------------- MODULE MC ----------------------------
(***************************************************************************
 * MODEL-CHECKING HARNESS
 *
 * Instantiates the abstract constants with a tiny network that still
 * exercises both fast (80%) and slow (60%) paths. Whitepaper §1.5 describes
 * the underlying model assumptions—partial synchrony, known validator set.
 ***************************************************************************)
EXTENDS MainProtocol, TLC

CONSTANTS v1, v2, v3, v4, b0, b1, b2, b3, b4, b5, nullBlock

\* Stake distribution: v1 (40%), v2 (30%), v3 (20%), v4 (10%).
\* This allows for one Byzantine validator (e.g., v4) with <20% stake.
MC_StakeMap == [v \in Validators |->
                    CASE v = v1 -> 40
                    [] v = v2 -> 30
                    [] v = v3 -> 20
                    [] v = v4 -> 10
                    [] OTHER -> 0]

\* Stake-weighted leader schedule constant for WindowSize = 2
MC_LeaderSchedule == [s \in Slots |->
                        CASE s = 0 -> v1
                        [] s = 1 -> v2
                        [] s = 2 -> v2  \* Leader for slot 2 should be same as slot 1 due to WindowSize = 2
                        [] OTHER -> v1]

=============================================================================
