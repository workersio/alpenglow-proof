---------------------------- MODULE Certificates ----------------------------

EXTENDS Naturals, FiniteSets, Messages, Sequences

(*
 Alpenglow WP v1.1 alignment (citations point to exact locations):

 - Fast vs. slow thresholds:
   • Fast-finalization: NotarVote Σ ≥ 80%; all other certs at Σ ≥ 60%.
     (Table 6, p.20; §2.4–§2.6)
   • One-round @80% and two-round @60% run in parallel; latency min(δ80%, 2δ60%).
     (Abstract p.1; §1.3 p.6; §2.6 p.22–25)

 - Stake model & finiteness:
   • Validators (nodes) are finite and fixed within an epoch; each has positive stake ρ_i > 0.
     (§1.5 “Node”, “Epoch”, “Stake”, p.8–10 incl. “Stake” p.9)

 - Fault assumptions using these thresholds:
   • Safety with <20% byzantine (Assumption 1); extra crash tolerance up to an additional 20% under Assumptions 2–3.
     (§1.2 p.4–5; §2.11 p.38–39)  :contentReference[oaicite:17]{index=17}
   • Safety and liveness results rely on the 80/60 machinery (Theorem 1 p.32; Theorem 2 p.37).
     (§2.9–§2.10)  :contentReference[oaicite:18]{index=18}

 - Modeling note:
   • Paper uses stake sums Σ over sets; enumeration order is irrelevant. Any sequence witnessing a bijection with S is fine.
     (Table 6 p.20; global set-based reasoning)  :contentReference[oaicite:19]{index=19}
*)

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

(* Block (paper-aligned)
Representation: b = { ⟨s,t,z_t,r_t,M_t,σ_t⟩ : t=1..k }, with z_k=1 and z_t=0 for t<k. §2.1, Def. 3, p.15. 
Slot/parent: slot(b)=s; M=(M_1..M_k) includes slot(parent(b)) and hash(parent(b)). §2.1, Def. 3, p.15. 
Hash: hash(b)=Merkle root over r_1..r_k padded to next power‑of‑two leaves (double‑Merkle: shreds→slice root r_t; slice roots→block root). §2.1, Fig. 2 & Def. 4, p.14–15. 
Slices/Shreds (context): each slice t is RS‑coded into Γ shreds; any γ suffice; each shred carries a Merkle path to r_t and leader sig on Slice(s,t,z_t,r_t). §2.1, Defs. 1–2 & §2.2, p.14–17. 
Validity invariants to model: z_k=1 ∧ ∀t<k: z_t=0; slot(parent(b)) < slot(b); hash(parent(b)) matches the parent link encoded in M. §2.1, Defs. 3–5, p.15–16. 
Interface to voting: on first complete block for slot s, emit Block(s, hash(b), hash(parent(b))) to Pool/Votor. §2.3, Def. 10, p.19. 
*)

TotalStake ==
  LET vals == DOMAIN StakeMap IN
  IF vals = {} THEN 0
  ELSE
    LET RECURSIVE Sum(_)
        Sum(S) ==
          IF S = {} THEN 0
          ELSE LET v == CHOOSE x \in S : TRUE
               IN  StakeMap[v] + Sum(S \ {v})
    IN  Sum(vals)


CalculateStake(validatorSet) ==
    LET vals == validatorSet \cap DOMAIN StakeMap
    IN IF vals = {} THEN 0
        ELSE
        LET RECURSIVE Sum(_)
            Sum(S) ==
                IF S = {} THEN 0
                ELSE LET v == CHOOSE x \in S : TRUE
                    IN StakeMap[v] + Sum(S \ {v})
        IN Sum(vals)

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
