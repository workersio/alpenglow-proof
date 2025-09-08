---------------------------- MODULE Stake ----------------------------
EXTENDS Common, Integers

CONSTANTS V

\* Hardcoded stake distribution for model checking
\* Validator 1 -> 10%, 2 -> 20%, 3 -> 30%, 4 -> 40%
rho[v \in V] == v

Weight(S) ==
    LET totalStake == 10  \* 1 + 2 + 3 + 4 = 10
    IN IF S = {} THEN 0 
       ELSE LET sumStake == SumOver(rho, S)
            IN (sumStake * 100) \div totalStake

GE60(S) ==
    Weight(S) >= 60

GE80(S) ==
    Weight(S) >= 80

ValidatorSet ==
    V

GetStake(v) ==
    rho[v]

TotalStake ==
    10

HasSuperMajority(S) ==
    GE60(S)

HasFastFinalizationQuorum(S) ==
    GE80(S)

QuorumSize ==
    60

FastQuorumSize ==
    80

====================================