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

\* Window-indexed leader function (WindowLeader) for WindowSize = 2
\* WindowIndex(0) = 0; WindowIndex(1) = 0; WindowIndex(2) = 0.
\* Make the first window's leader v4 (so slots 1 and 2 map to v4).
MC_WindowLeader == [k \in Nat |->
                        CASE k = 0 -> v4
                        [] OTHER -> v1]

\* [UNCOMMENT FOR TESTING] Test scenario for skipped immediate predecessor slot
\* SkippedSlotInit ==
\*     /\ Init
\*     /\ byzantineNodes = {v4}

\* SkippedSlotSpec == SkippedSlotInit /\ [][Next]_vars /\ Fairness

=============================================================================
