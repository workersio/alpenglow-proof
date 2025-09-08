---------------------------- MODULE Pool ----------------------------
EXTENDS Common, Stake, CryptoAbstraction, Certificates

VARIABLES
    poolVotes,
    poolCertificates

PoolVars == <<poolVotes, poolCertificates>>

InitPool ==
    /\ poolVotes = {}
    /\ poolCertificates = {}

HasVoteFromValidator(v, slot, voteType) ==
    \E vote \in poolVotes :
        /\ vote.validator = v
        /\ vote.slot = slot
        /\ vote.type = voteType

AddVoteToPool(vote) ==
    IF HasVoteFromValidator(vote.validator, vote.slot, vote.type)
    THEN UNCHANGED poolVotes
    ELSE poolVotes' = poolVotes \union {vote}

GetVotesForCertType(certType, hash) ==
    CASE certType = "NotarizationCert" ->
            {v \in poolVotes : IsNotarVote(v) /\ v.hash = hash /\ v.slot = "s0"}
      [] certType = "FastFinalizationCert" ->
            {v \in poolVotes : IsNotarVote(v) /\ v.hash = hash /\ v.slot = "s0"}
      [] certType = "FinalizationCert" ->
            {v \in poolVotes : IsFinalVote(v) /\ v.slot = "s0"}
      [] OTHER -> {}

HasCertificateOfType(certType, hash) ==
    \E cert \in poolCertificates :
        CASE certType = "NotarizationCert" ->
                IsNotarizationCert(cert) /\ cert.hash = hash
          [] certType = "FastFinalizationCert" ->
                IsFastFinalizationCert(cert) /\ cert.hash = hash
          [] certType = "FinalizationCert" ->
                IsFinalizationCert(cert)
          [] OTHER -> FALSE

TryCreateNotarizationCert(h) ==
    LET votes == GetVotesForCertType("NotarizationCert", h)
    IN /\ CanCreateNotarizationCert(votes, h)
       /\ ~HasCertificateOfType("NotarizationCert", h)
       /\ poolCertificates' = poolCertificates \union {NotarizationCert(h, votes)}

TryCreateFastFinalizationCert(h) ==
    LET votes == GetVotesForCertType("FastFinalizationCert", h)
    IN /\ CanCreateFastFinalizationCert(votes, h)
       /\ ~HasCertificateOfType("FastFinalizationCert", h)
       /\ poolCertificates' = poolCertificates \union {FastFinalizationCert(h, votes)}

TryCreateFinalizationCert ==
    LET votes == GetVotesForCertType("FinalizationCert", "-")
    IN /\ CanCreateFinalizationCert(votes)
       /\ ~HasCertificateOfType("FinalizationCert", "-")
       /\ poolCertificates' = poolCertificates \union {FinalizationCert(votes)}

GenerateCertificates(Blocks) ==
    \/ \E h \in Blocks :
        /\ TryCreateNotarizationCert(h)
        /\ UNCHANGED poolVotes
    \/ \E h \in Blocks :
        /\ TryCreateFastFinalizationCert(h)
        /\ UNCHANGED poolVotes
    \/ /\ TryCreateFinalizationCert
       /\ UNCHANGED poolVotes

HasNotarizationCert(h) ==
    HasCertificateOfType("NotarizationCert", h)

HasFastFinalizationCert(h) ==
    HasCertificateOfType("FastFinalizationCert", h)

HasFinalizationCert ==
    HasCertificateOfType("FinalizationCert", "-")

GetNotarizedBlocks ==
    {cert.hash : cert \in {c \in poolCertificates : IsNotarizationCert(c)}}

GetUniqueNotarizedBlock ==
    IF Cardinality(GetNotarizedBlocks) = 1
    THEN CHOOSE h \in GetNotarizedBlocks : TRUE
    ELSE "-"

=======================================================================