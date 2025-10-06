---------------------------- MODULE Certificates ----------------------------

EXTENDS Naturals, FiniteSets, Messages, Sequences


CONSTANTS
    StakeMap

ASSUME
    /\ StakeMap \in [Validators -> Nat \ {0}]

FastFinalThreshold == 80
DefaultThreshold  == 60

EnumerateSet(S) ==
    CHOOSE seq \in Seq(S) :
        /\ Len(seq) = Cardinality(S)
        /\ {seq[i] : i \in 1 .. Len(seq)} = S
        /\ \A i, j \in 1 .. Len(seq) : i # j => seq[i] # seq[j]

TotalStake == 
    LET vals == DOMAIN StakeMap
    IN IF vals = {} THEN 0
       ELSE LET Sum[S \in SUBSET vals] == 
                IF S = {} THEN 0
                ELSE LET v == CHOOSE x \in S : TRUE
                     IN StakeMap[v] + Sum[S \ {v}]
            IN Sum[vals]

CalculateStake(validatorSet) ==
    LET vals == validatorSet \cap DOMAIN StakeMap
    IN IF vals = {} THEN 0
       ELSE LET Sum[S \in SUBSET vals] == 
                IF S = {} THEN 0
                ELSE LET v == CHOOSE x \in S : TRUE
                     IN StakeMap[v] + Sum[S \ {v}]
            IN Sum[vals]

UniqueValidators(votes) ==
    {v.validator : v \in votes}

StakeFromVotes(votes) ==
    CalculateStake(UniqueValidators(votes))

MeetsThreshold(stake, thresholdPercent) ==
    stake * 100 >= TotalStake * thresholdPercent

VotesFor(votes, slot, blockHash, types) ==
    {v \in votes :
        /\ v.slot = slot
        /\ v.blockHash = blockHash
        /\ v.type \in types}

CanCreateFastFinalizationCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes : 
        /\ v.type = "NotarVote"
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), FastFinalThreshold)

CanCreateNotarizationCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes :
        /\ v.type = "NotarVote"
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)


CanCreateNotarFallbackCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes :
        /\ v.slot = slot
        /\ IsVoteForBlock(v, blockHash)}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

CanCreateSkipCert(votes, slot) ==
    LET relevantVotes == {v \in votes :
        /\ IsSkipVote(v)
        /\ v.slot = slot}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

CanCreateFinalizationCert(votes, slot) ==
    LET relevantVotes == {v \in votes :
        /\ v.type = "FinalVote"
        /\ v.slot = slot}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)


CanonicalizeSkipVotes(votes, slot) ==
    LET S == {v \in votes : /\ IsSkipVote(v) /\ v.slot = slot}
        V == {v.validator : v \in S}
        Pick(val) ==
            IF \E x \in S : /\ x.validator = val /\ x.type = "SkipFallbackVote"
            THEN CHOOSE x \in S : /\ x.validator = val /\ x.type = "SkipFallbackVote"
            ELSE CHOOSE x \in S : /\ x.validator = val /\ x.type = "SkipVote"
    IN { Pick(val) : val \in V }

CreateFastFinalizationCert(votes, slot, blockHash) ==
    [type |-> "FastFinalizationCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type = "NotarVote" /\ v.slot = slot /\ v.blockHash = blockHash}]

CreateNotarizationCert(votes, slot, blockHash) ==
    [type |-> "NotarizationCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type = "NotarVote" /\ v.slot = slot /\ v.blockHash = blockHash}]

CreateNotarFallbackCert(votes, slot, blockHash) ==
    [type |-> "NotarFallbackCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : /\ v.slot = slot /\ IsVoteForBlock(v, blockHash)}]


CreateSkipCert(votes, slot) ==
    [type |-> "SkipCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> CanonicalizeSkipVotes(votes, slot)]


CreateFinalizationCert(votes, slot) ==
    [type |-> "FinalizationCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> {v \in votes : 
        v.type = "FinalVote" /\ v.slot = slot}]


IsValidCertificate(cert) ==
    LET RelevantVotes ==
            CASE cert.type = "FastFinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarFallbackCert" ->
                     {v \in cert.votes : /\ v.slot = cert.slot /\ IsVoteForBlock(v, cert.blockHash)}
               [] cert.type = "SkipCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"SkipVote", "SkipFallbackVote"})
               [] cert.type = "FinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"FinalVote"})
               [] OTHER -> {}
        stake == StakeFromVotes(RelevantVotes)
    IN /\ cert.type \in CertificateType
       /\ cert.slot \in Slots
       /\ (\A v \in cert.votes : IsValidVote(v))  \* defensive typing check
       /\ CASE cert.type = "FastFinalizationCert" ->
               /\ cert.blockHash \in BlockHashes
               /\ MeetsThreshold(stake, FastFinalThreshold)
          [] cert.type \in {"NotarizationCert", "NotarFallbackCert"} ->
               /\ cert.blockHash \in BlockHashes
               /\ MeetsThreshold(stake, DefaultThreshold)
          [] cert.type = "SkipCert" ->
               /\ cert.blockHash = NoBlock
               /\ MeetsThreshold(stake, DefaultThreshold)
          [] cert.type = "FinalizationCert" ->
               /\ cert.blockHash = NoBlock
               /\ MeetsThreshold(stake, DefaultThreshold)
          [] OTHER -> FALSE

CertificateWellFormed(cert) ==
    LET RelevantVotes ==
            CASE cert.type = "FastFinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarFallbackCert" ->
                     {v \in cert.votes : /\ v.slot = cert.slot /\ IsVoteForBlock(v, cert.blockHash)}
               [] cert.type = "SkipCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"SkipVote", "SkipFallbackVote"})
               [] cert.type = "FinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"FinalVote"})
               [] OTHER -> {}
    IN cert.votes \subseteq RelevantVotes

AllCertificatesValid(certificates) ==
    \A cert \in certificates : IsValidCertificate(cert)

FastPathImplication(certificates) ==
    \A fastCert \in certificates :
        fastCert.type = "FastFinalizationCert" =>
        \E notarCert \in certificates :
            /\ notarCert.type = "NotarizationCert"
            /\ notarCert.slot = fastCert.slot
            /\ notarCert.blockHash = fastCert.blockHash
            /\ notarCert.votes \subseteq fastCert.votes

FastImpliesNotarThresholdOnly(certificates) ==
    \A fastCert \in certificates :
        fastCert.type = "FastFinalizationCert" =>
        \E notarCert \in certificates :
            /\ notarCert.type = "NotarizationCert"
            /\ notarCert.slot = fastCert.slot
            /\ notarCert.blockHash = fastCert.blockHash

SkipVsBlockCertExclusion(certificates) ==
    LET hasSkip == \E c \in certificates : c.type = "SkipCert"
        hasBlock == \E c \in certificates :
                        c.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}
    IN ~(hasSkip /\ hasBlock)

\* Optional helper: all certificates in a set are structurally well-formed
AllCertificatesWellFormed(certificates) ==
    \A cert \in certificates : CertificateWellFormed(cert)

=============================================================================
