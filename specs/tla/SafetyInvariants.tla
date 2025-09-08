---------------------------- MODULE SafetyInvariants ----------------------------
EXTENDS Common, Stake, CryptoAbstraction, Certificates, Pool, VotorCore

\* INVARIANT 1: No Double Finalization
\* At most one block can be finalized per slot
NoDoubleFinalization ==
    \A h1, h2 \in finalizedBlocks :
        h1 = h2

\* INVARIANT 2: Certificate Uniqueness  
\* At most one certificate of each type per slot/hash
CertUnique ==
    /\ \A c1, c2 \in poolCertificates :
        (IsNotarizationCert(c1) /\ IsNotarizationCert(c2) /\ c1.hash = c2.hash) => c1 = c2
    /\ \A c1, c2 \in poolCertificates :
        (IsFastFinalizationCert(c1) /\ IsFastFinalizationCert(c2) /\ c1.hash = c2.hash) => c1 = c2
    /\ \A c1, c2 \in poolCertificates :
        (IsFinalizationCert(c1) /\ IsFinalizationCert(c2)) => c1 = c2

\* INVARIANT 3: No Equivocation
\* Each validator casts at most one vote per (slot, type)
NoEquivocation ==
    \A v \in V :
        /\ \A vote1, vote2 \in poolVotes :
            (vote1.validator = v /\ vote2.validator = v /\ 
             vote1.slot = vote2.slot /\ vote1.type = vote2.type) =>
            vote1 = vote2

\* INVARIANT 4: Certificate Type Mutual Exclusion
\* For slot s0, only one type of finalization certificate can exist
CertTypeMutualExclusion ==
    LET hasFastFin == \E c \in poolCertificates : IsFastFinalizationCert(c)
        hasRegularFin == \E c \in poolCertificates : IsFinalizationCert(c)
    IN ~(hasFastFin /\ hasRegularFin)

\* Non-vacuity properties
SomeCertificateProduced ==
    sawAnyCert

SomeFinalizationOccurred ==
    sawFinalization

=======================================================================