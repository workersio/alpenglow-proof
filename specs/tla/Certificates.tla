---------------------------- MODULE Certificates ----------------------------
EXTENDS Common, CryptoAbstraction, Stake

Certificate(Blocks) ==
    [type: {"NotarizationCert", "FastFinalizationCert", "FinalizationCert"},
     slot: {"s0"},
     hash: Blocks \union {"-"},
     votes: SUBSET Vote(Blocks),
     signers: SUBSET V]

NotarizationCert(h, votes) ==
    [type |-> "NotarizationCert",
     slot |-> "s0",
     hash |-> h,
     votes |-> votes,
     signers |-> GetSigners(votes)]

FastFinalizationCert(h, votes) ==
    [type |-> "FastFinalizationCert",
     slot |-> "s0",
     hash |-> h,
     votes |-> votes,
     signers |-> GetSigners(votes)]

FinalizationCert(votes) ==
    [type |-> "FinalizationCert",
     slot |-> "s0",
     hash |-> "-",
     votes |-> votes,
     signers |-> GetSigners(votes)]

IsNotarizationCert(cert) ==
    cert.type = "NotarizationCert"

IsFastFinalizationCert(cert) ==
    cert.type = "FastFinalizationCert"

IsFinalizationCert(cert) ==
    cert.type = "FinalizationCert"

CertificateKey(cert) ==
    IF cert.type = "FinalizationCert"
    THEN <<cert.type, cert.slot>>
    ELSE <<cert.type, cert.slot, cert.hash>>

ValidNotarizationCert(cert) ==
    /\ IsNotarizationCert(cert)
    /\ cert.hash # "-"
    /\ \A v \in cert.votes : 
        /\ IsNotarVote(v)
        /\ v.hash = cert.hash
        /\ v.slot = cert.slot
    /\ cert.signers = GetSigners(cert.votes)
    /\ GE60(cert.signers)

ValidFastFinalizationCert(cert) ==
    /\ IsFastFinalizationCert(cert)
    /\ cert.hash # "-"
    /\ \A v \in cert.votes :
        /\ IsNotarVote(v)
        /\ v.hash = cert.hash
        /\ v.slot = cert.slot
    /\ cert.signers = GetSigners(cert.votes)
    /\ GE80(cert.signers)

ValidFinalizationCert(cert) ==
    /\ IsFinalizationCert(cert)
    /\ cert.hash = "-"
    /\ \A v \in cert.votes :
        /\ IsFinalVote(v)
        /\ v.slot = cert.slot
    /\ cert.signers = GetSigners(cert.votes)
    /\ GE60(cert.signers)

ValidCertificate(cert) ==
    \/ ValidNotarizationCert(cert)
    \/ ValidFastFinalizationCert(cert)
    \/ ValidFinalizationCert(cert)

CanCreateNotarizationCert(votes, h) ==
    LET notarVotes == {v \in votes : IsNotarVote(v) /\ v.hash = h /\ v.slot = "s0"}
        signers == GetSigners(notarVotes)
    IN GE60(signers)

CanCreateFastFinalizationCert(votes, h) ==
    LET notarVotes == {v \in votes : IsNotarVote(v) /\ v.hash = h /\ v.slot = "s0"}
        signers == GetSigners(notarVotes)
    IN GE80(signers)

CanCreateFinalizationCert(votes) ==
    LET finalVotes == {v \in votes : IsFinalVote(v) /\ v.slot = "s0"}
        signers == GetSigners(finalVotes)
    IN GE60(signers)

=======================================================================