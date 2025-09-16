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
    RotorMinRelayStake    \* Minimum total stake covered by a relay set

ASSUME
    /\ RotorFanout \in Nat \ {0}
    /\ RotorMinRelayStake \in Nat \ {0}
    /\ RotorMinRelayStake <= TotalStake

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
        CHOOSE sample \in SUBSET needers :
            /\ sample # {}
            /\ Cardinality(sample) <= RotorFanout
            /\ (nextLeader \in needers => nextLeader \in sample)
            /\ CalculateStake(sample) >= RotorMinRelayStake

=============================================================================
