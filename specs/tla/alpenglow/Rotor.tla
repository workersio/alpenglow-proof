---------------------------- MODULE Rotor ----------------------------
(***************************************************************************
 * ABSTRACT ROTOR BROADCAST MODEL
 *
 * Simplifies the erasure-coded dissemination pipeline from Whitepaper §2.2.
 * Instead of modelling shreds, we require that each sampling step selects a
 * stake-weighted relay set (fanout bounded, next leader prioritised) that
 * eventually delivers the full block to every validator.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Certificates

CONSTANTS
    RotorFanout,          \* Number of relays contacted per dissemination step
    RotorMinRelayStake,   \* Minimum total stake covered by a relay set
    RotorGamma            \* Minimum number of correct relays required for success

ASSUME
    /\ RotorFanout \in Nat \ {0}
    /\ RotorMinRelayStake \in Nat \ {0}
    /\ RotorMinRelayStake <= TotalStake
    /\ RotorGamma \in Nat \ {0}

\* Candidate relay sets that satisfy the qualitative constraints quoted in
\* Whitepaper §2.2 (Definition 6 and Lemma 7).
RotorCandidates(needers, nextLeader) ==
    {sample \in SUBSET needers :
        /\ sample # {}
        /\ Cardinality(sample) <= RotorFanout
        /\ (nextLeader \in needers => nextLeader \in sample)
        /\ CalculateStake(sample) >= RotorMinRelayStake}

\* Assumption: whenever dissemination is needed, the stake-weighted sampling
\* layer can supply at least one candidate relay set satisfying the above
\* constraints. This reflects the over-provisioning argument in Lemma 7.
ASSUME RotorRelayCoverage ==
    \A needers \in SUBSET Validators :
        needers # {} => (\A nextLeader \in Validators :
            RotorCandidates(needers, nextLeader) # {})

(***************************************************************************
 * RotorSelect(block, needers, nextLeader)
 *
 * - needers: validators that still require the block
 * - nextLeader: leader of the next slot (Section 2.2 notes they are prioritised)
 *
 * The returned set is:
 *   * Non-empty when dissemination is needed
 *   * Limited by RotorFanout
 *   * Includes the next leader whenever it still needs the block
 *   * Covers at least RotorMinRelayStake stake (stake-proportional fanout)
 ***************************************************************************)

RotorSelect(block, needers, nextLeader) ==
    IF needers = {} THEN {}
    ELSE
        CHOOSE sample \in RotorCandidates(needers, nextLeader) : TRUE

\* The constraints above encode the qualitative requirements in §2.2:
\*  - at least one relay forwards the block when someone still needs it;
\*  - the next leader is prioritised (fast handoff);
\*  - only a bounded number of relays send in each step (fanout);
\*  - the chosen set covers enough stake to remain resilient to faults.

=============================================================================
