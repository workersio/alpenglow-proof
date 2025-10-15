---------------------------- MODULE Certificates ----------------------------
(*
  Mapping & scope.
  - Stake-weighted voting and thresholds: 80% fast path, 60% otherwise
    (Section 2.4, Def. 11; Table 6, p.20–21). Certificates aggregate votes
    via aggregate signatures over validator sets (Section 1.6 “Aggregate
    Signature”, p.12), so each validator contributes at most once per cert.
    We model that explicitly.
*)
EXTENDS Naturals, FiniteSets, Messages, Sequences

CONSTANTS
    StakeMap
(*
  StakeMap: validator → positive stake fraction proxy.
  - Stake and validator set are fixed for an epoch (Section 1.5 “Stake”,
    p.9–10). We model stake as Nats and compare with percentages.
*)

ASSUME
    /\ StakeMap \in [Validators -> Nat \ {0}]

(*
  Thresholds per Table 6 (p.20–21):
   - Fast-finalization cert: 80% of NotarVote
   - All other certs: 60% of the relevant votes.
*)
FastFinalThreshold == 80
DefaultThreshold  == 60

(*
  Helper: enumerate a finite set as a sequence (deterministic choice is OK).
*)
EnumerateSet(S) ==
    CHOOSE seq \in Seq(S) :
        /\ Len(seq) = Cardinality(S)
        /\ {seq[i] : i \in 1 .. Len(seq)} = S
        /\ \A i, j \in 1 .. Len(seq) : i # j => seq[i] # seq[j]

(*
  TotalStake: Σ over validators; used for percentage tests.
  - Table 6 defines Σ as cumulative stake over a validator index set I.
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

(*
  CalculateStake: Σ stake over a validator set (subset of StakeMap domain).
*)
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

(*
  Vote → validator projection and stake-from-votes.
  - Certificates count each validator at most once (aggregate bitmaps,
    Table 6; message layout/Table 11 node bitmap hints, p.44–45). We thus
    deduplicate by validator before summing stake.
*)
UniqueValidators(votes) ==
    {v.validator : v \in votes}

StakeFromVotes(votes) ==
    CalculateStake(UniqueValidators(votes))

(*
  NoDupValidators: enforce at most one vote per validator inside a cert.
  - Mirrors “aggregate signature over a set I of signers” (Section 1.6;
    Table 6 definition of Σ over a set of indices I).
*)
NoDupValidators(votes) ==
    \A v1, v2 \in votes : (v1.validator = v2.validator) => v1 = v2

(*
  MeetsThreshold: stake ≥ θ% of TotalStake (percent thresholds per Table 6).
*)
MeetsThreshold(stake, thresholdPercent) ==
    stake * 100 >= TotalStake * thresholdPercent

(*
  Vote filters.
  - For Notar/NotarFallback we filter by (slot, blockHash).
  - For Skip/Final votes, the white paper defines them as slot-only
    (Table 5, p.20). We therefore provide a slot-only filter to avoid
    assuming a blockHash field exists for those vote types.
*)
VotesFor(votes, slot, blockHash, types) ==
    {v \in votes :
        /\ v.slot = slot
        /\ v.blockHash = blockHash
        /\ v.type \in types}

VotesForSlotOnly(votes, slot, types) ==
    {v \in votes :
        /\ v.slot = slot
        /\ v.type \in types}

(*
  Creatability conditions (mirrors Table 6, p.20–21):
   - Fast-Finalization: 80% NotarVote on (slot, block)
   - Notarization:     60% NotarVote on (slot, block)
   - Notar-Fallback:   60% NotarVote OR NotarFallbackVote on (slot, block)
   - Skip:             60% SkipVote OR SkipFallbackVote in slot
   - Finalization:     60% FinalVote in slot.
*)
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
        /\ IsVoteForBlock(v, blockHash)}  \* accepts NotarVote or NotarFallbackVote (Table 6).
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

CanCreateSkipCert(votes, slot) ==
    LET relevantVotes == VotesForSlotOnly(votes, slot, {"SkipVote","SkipFallbackVote"})
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

CanCreateFinalizationCert(votes, slot) ==
    LET relevantVotes == VotesForSlotOnly(votes, slot, {"FinalVote"})
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

(*
  CanonicalizeSkipVotes: per-validator choose SkipFallback if present,
  otherwise Skip. This respects Pool storage rules (first skip vote and
  first skip-fallback; Def. 12, p.20–21) but any 60% mix certifies (Table 6).
*)
CanonicalizeSkipVotes(votes, slot) ==
    LET S == {v \in votes : /\ IsSkipVote(v) /\ v.slot = slot}
        V == {v.validator : v \in S}
        Pick(val) ==
            IF \E x \in S : /\ x.validator = val /\ x.type = "SkipFallbackVote"
            THEN CHOOSE x \in S : /\ x.validator = val /\ x.type = "SkipFallbackVote"
            ELSE CHOOSE x \in S : /\ x.validator = val /\ x.type = "SkipVote"
    IN { Pick(val) : val \in V }

(*
  Constructors of certificate records (Table 6, p.20–21).
*)
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
     blockHash |-> NoBlock,  \* slot-only per Table 5.
     votes |-> CanonicalizeSkipVotes(votes, slot)]

CreateFinalizationCert(votes, slot) ==
    [type |-> "FinalizationCert",
     slot |-> slot,
     blockHash |-> NoBlock,  \* slot-only per Table 5.
     votes |-> {v \in votes : v.type = "FinalVote" /\ v.slot = slot}]

(*
  Certificate validity: typing + relevant votes + threshold.
  - Types and thresholds: Table 6 (p.20–21).
  - Slot domain & vote well-typedness: Sections 2.4–2.5 (pp.19–21).
  - We additionally enforce NoDupValidators to reflect aggregate signature
    semantics over a validator set I (Section 1.6, p.12).
*)
IsValidCertificate(cert) ==
    LET RelevantVotes ==
            CASE cert.type = "FastFinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarFallbackCert" ->
                     {v \in cert.votes : /\ v.slot = cert.slot /\ IsVoteForBlock(v, cert.blockHash)}
               [] cert.type = "SkipCert" ->
                     VotesForSlotOnly(cert.votes, cert.slot, {"SkipVote", "SkipFallbackVote"})
               [] cert.type = "FinalizationCert" ->
                     VotesForSlotOnly(cert.votes, cert.slot, {"FinalVote"})
               [] OTHER -> {}
        stake == StakeFromVotes(RelevantVotes)
    IN /\ cert.type \in CertificateType
       /\ cert.slot \in Slots
       /\ (\A v \in cert.votes : IsValidVote(v))     \* defensive typing check
       /\ NoDupValidators(cert.votes)                \* aggregate set of signers.
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

(*
  Well-formedness: a certificate doesn’t include irrelevant votes and has
  one vote per validator (aggregate-set discipline; Section 1.6, Table 6).
*)
CertificateWellFormed(cert) ==
    LET RelevantVotes ==
            CASE cert.type = "FastFinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarFallbackCert" ->
                     {v \in cert.votes : /\ v.slot = cert.slot /\ IsVoteForBlock(v, cert.blockHash)}
               [] cert.type = "SkipCert" ->
                     VotesForSlotOnly(cert.votes, cert.slot, {"SkipVote", "SkipFallbackVote"})
               [] cert.type = "FinalizationCert" ->
                     VotesForSlotOnly(cert.votes, cert.slot, {"FinalVote"})
               [] OTHER -> {}
    IN /\ cert.votes \subseteq RelevantVotes
       /\ NoDupValidators(cert.votes)

(*
  Convenience predicates over sets of certificates.
*)
AllCertificatesValid(certificates) ==
    \A cert \in certificates : IsValidCertificate(cert)

AllCertificatesWellFormed(certificates) ==
    \A cert \in certificates : CertificateWellFormed(cert)

(*
  Fast path ⇒ Notarization + Notar-Fallback exist for (slot, block).
  - Pool emits both once thresholds hit (Def. 13; note under the table,
    p.21: fast → notar → notar-fallback). We *do not* require subset
    containment of signer sets (not stated/needed).  [FIXED: removed
    too-strong subset constraint.]
*)
FastImpliesNotarAndFallback(certificates) ==
    \A fastCert \in certificates :
        fastCert.type = "FastFinalizationCert" =>
        /\ \E notarCert \in certificates :
             /\ notarCert.type = "NotarizationCert"
             /\ notarCert.slot = fastCert.slot
             /\ notarCert.blockHash = fastCert.blockHash
        /\ \E nfCert \in certificates :
             /\ nfCert.type = "NotarFallbackCert"
             /\ nfCert.slot = fastCert.slot
             /\ nfCert.blockHash = fastCert.blockHash

(*
  Skip vs. block certificate exclusion is **per slot** (Lemmas 21 & 26):
  - If a block in slot s is fast- or slow-finalized/notarized, a skip cert
    for slot s cannot exist; but skip in other slots is fine. [FIXED: the
    original predicate was global and too strong.] (Lemmas 21 & 26,
    pp.28–31).
*)
SkipVsBlockCertExclusionPerSlot(certificates) ==
    \A s \in Slots :
      LET hasSkip_s ==
            \E c \in certificates : /\ c.type = "SkipCert" /\ c.slot = s
          hasBlock_s ==
            \E c \in certificates :
                /\ c.slot = s
                /\ c.type \in {"NotarizationCert","NotarFallbackCert","FastFinalizationCert"}
      IN ~(hasSkip_s /\ hasBlock_s)

(*
  Back-compat predicates used by pool-level invariants.
  Paper basis: Table 6 (pp.20–21) + Def. 13 (Pool), and Lemmas 21 & 26 (pp.28–31).
*)

FastPathImplication(certificates) ==
    \A fastCert \in certificates :
        fastCert.type = "FastFinalizationCert" =>
        \E notarCert \in certificates :
            /\ notarCert.type = "NotarizationCert"
            /\ notarCert.slot = fastCert.slot
            /\ notarCert.blockHash = fastCert.blockHash
            /\ notarCert.votes \subseteq fastCert.votes
(*
  Note: the subset condition is an implementation-strengthening not required
  by the paper. If your implementation sometimes builds the two certs from
  different but threshold-satisfying vote multisets, prefer:
  UniqueValidators(notarCert.votes) \subseteq UniqueValidators(fastCert.votes).
*)

FastImpliesNotarThresholdOnly(certificates) ==
    \A fastCert \in certificates :
        fastCert.type = "FastFinalizationCert" =>
        \E notarCert \in certificates :
            /\ notarCert.type = "NotarizationCert"
            /\ notarCert.slot = fastCert.slot
            /\ notarCert.blockHash = fastCert.blockHash

SkipVsBlockCertExclusion(certificates) ==
    LET hasSkip ==
            \E c \in certificates : c.type = "SkipCert"
        hasBlock ==
            \E c \in certificates :
                 c.type \in {"NotarizationCert","NotarFallbackCert","FastFinalizationCert"}
    IN ~(hasSkip /\ hasBlock)

=============================================================================
