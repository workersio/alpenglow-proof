---------------------------- MODULE VotorCore ----------------------------
EXTENDS Common, Stake, CryptoAbstraction, Certificates, Pool, TLC

CONSTANTS
    Blocks,
    ActiveValidators  \* Set of validators that will participate

VARIABLES
    validatorState,
    blockArrivals,
    timeoutFired,
    finalizedBlocks,
    sawAnyCert,
    sawFinalization

vars == <<poolVotes, poolCertificates, validatorState, blockArrivals, timeoutFired, finalizedBlocks, sawAnyCert, sawFinalization>>

Init ==
    /\ InitPool
    /\ validatorState = [v \in V |-> 
        [notarVoted |-> FALSE,
         finalVoted |-> FALSE,
         skipVoted |-> FALSE]]
    /\ blockArrivals = {}
    /\ timeoutFired = FALSE
    /\ finalizedBlocks = {}
    /\ sawAnyCert = FALSE
    /\ sawFinalization = FALSE

BlockArrives(h, p) ==
    /\ blockArrivals' = blockArrivals \union {[hash |-> h, parent |-> p]}
    /\ UNCHANGED <<poolVotes, poolCertificates, validatorState, timeoutFired, finalizedBlocks, sawAnyCert, sawFinalization>>

TimeoutFires ==
    /\ ~timeoutFired
    /\ timeoutFired' = TRUE
    /\ UNCHANGED <<poolVotes, poolCertificates, validatorState, blockArrivals, finalizedBlocks, sawAnyCert, sawFinalization>>

ValidatorCastsNotarVote(v, h) ==
    /\ v \in ActiveValidators  \* Only active validators can vote
    /\ \E b \in blockArrivals : b.hash = h
    /\ ~validatorState[v].notarVoted
    /\ ~validatorState[v].skipVoted
    /\ AddVoteToPool(NotarVote(v, "s0", h))
    /\ validatorState' = [validatorState EXCEPT ![v].notarVoted = TRUE]
    /\ UNCHANGED <<poolCertificates, blockArrivals, timeoutFired, finalizedBlocks, sawAnyCert, sawFinalization>>

ValidatorCastsFinalVote(v) ==
    /\ v \in ActiveValidators  \* Only active validators can vote
    /\ \E cert \in poolCertificates : IsNotarizationCert(cert)
    /\ ~validatorState[v].finalVoted
    /\ AddVoteToPool(FinalVote(v, "s0"))
    /\ validatorState' = [validatorState EXCEPT ![v].finalVoted = TRUE]
    /\ UNCHANGED <<poolCertificates, blockArrivals, timeoutFired, finalizedBlocks, sawAnyCert, sawFinalization>>

ValidatorCastsSkipVote(v) ==
    /\ v \in ActiveValidators  \* Only active validators can vote
    /\ timeoutFired
    /\ ~validatorState[v].notarVoted
    /\ ~validatorState[v].skipVoted
    /\ AddVoteToPool(SkipVote(v, "s0"))
    /\ validatorState' = [validatorState EXCEPT ![v].skipVoted = TRUE]
    /\ UNCHANGED <<poolCertificates, blockArrivals, timeoutFired, finalizedBlocks, sawAnyCert, sawFinalization>>

TryFinalize ==
    \/ \E cert \in poolCertificates :
        /\ IsFastFinalizationCert(cert)
        /\ cert.hash \notin finalizedBlocks
        /\ finalizedBlocks' = finalizedBlocks \union {cert.hash}
        /\ sawFinalization' = TRUE
        /\ UNCHANGED <<poolVotes, poolCertificates, validatorState, blockArrivals, timeoutFired, sawAnyCert>>
    \/ /\ \E cert \in poolCertificates : IsFinalizationCert(cert)
       /\ Cardinality(GetNotarizedBlocks) = 1
       /\ LET h == GetUniqueNotarizedBlock
          IN /\ h # "-"
             /\ h \notin finalizedBlocks
             /\ finalizedBlocks' = finalizedBlocks \union {h}
       /\ sawFinalization' = TRUE
       /\ UNCHANGED <<poolVotes, poolCertificates, validatorState, blockArrivals, timeoutFired, sawAnyCert>>

GenerateCertsWrapper ==
    /\ GenerateCertificates(Blocks)
    /\ sawAnyCert' = IF poolCertificates' # poolCertificates THEN TRUE ELSE sawAnyCert
    /\ UNCHANGED <<validatorState, blockArrivals, timeoutFired, finalizedBlocks, sawFinalization>>

Next ==
    \/ \E h \in Blocks, p \in Blocks : BlockArrives(h, p)
    \/ TimeoutFires
    \/ \E v \in V, h \in Blocks : ValidatorCastsNotarVote(v, h)
    \/ \E v \in V : ValidatorCastsFinalVote(v)
    \/ \E v \in V : ValidatorCastsSkipVote(v)
    \/ GenerateCertsWrapper
    \/ TryFinalize

Spec == Init /\ [][Next]_vars

=======================================================================