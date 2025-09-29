---------------------------- MODULE Certificates ----------------------------
(***************************************************************************
 * CERTIFICATE GENERATION AND STAKE AGGREGATION FOR ALPENGLOW
 *
 * What this module specifies and why (whitepaper anchors):
 * - Votes & Certificates (§2.4): thresholds and message families
 *   • Table 5 defines vote messages; Table 6 defines certificate types.
 *   • Fast path: ≥80% stake on NotarVote finalizes in one round.
 *   • Slow path: ≥60% stake thresholds for notarization, fallback,
 *     skip, and finalization; two rounds finalize (§2.4, §2.6).
 * - Pool rules (§2.5, Definitions 12–13): count-once-per-slot per validator
 *   and when/what certificates are produced and stored/broadcast.
 * - Finalization semantics (§2.5, Definition 14):
 *   • Fast-finalization certificate finalizes its block b.
 *   • Finalization certificate on slot s finalizes the unique notarized
 *     block in s (slow path); ancestors finalize first.
 * - Aggregate signatures (§1.6): Certificates are conceptually aggregated
 *   signatures over the same message; here we model them as sets of votes
 *   whose total stake Σ crosses the threshold (Table 6).
 *
 * This file encodes the threshold checks and well-formedness for those
 * certificates. Each validator’s stake contributes at most once per slot
 * (Definition 12’s “count once” rule), and Σ is computed as the sum of the
 * voting validators’ stakes (Table 6: Σ = Σ_i ρ_i).
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Messages, Sequences

\* ============================================================================
\* CONSTANTS
\* ============================================================================

CONSTANTS
    StakeMap        \* ρ: Validators → Nat\{0}; per-validator stake weights (Table 6)

ASSUME
    /\ StakeMap \in [Validators -> Nat \ {0}]  \* Every validator has positive stake ρ_v

\* ============================================================================
\* THRESHOLD PARAMETERS (avoid magic numbers)
\* ============================================================================

(***************************************************************************
 * Thresholds per whitepaper Table 6 (Votes & Certificates, §2.4) and the
 * latency discussion in §2.6: fast (80%) vs slow (60% + second round).
 ***************************************************************************)
FastFinalThreshold == 80
DefaultThreshold  == 60

\* ============================================================================
\* STAKE CALCULATIONS
\* ============================================================================

(***************************************************************************
 * Count-once-per-slot (Pool, Definition 12 in §2.5)
 * - Pool stores at most one initial vote (notarization or skip) per validator
 *   per slot; a bounded number of fallback votes are also stored (§2.5).
 * - Certificate stake Σ must count each validator’s ρ_v at most once in slot s
 *   even if both initial and fallback votes exist (Table 6; Def. 12).
 * This section implements the “count once” policy by deduplicating validators
 * prior to stake summation.
 ***************************************************************************)

EnumerateSet(S) ==
    CHOOSE seq \in Seq(S) :
        /\ Len(seq) = Cardinality(S)
        /\ {seq[i] : i \in 1 .. Len(seq)} = S
        /\ \A i, j \in 1 .. Len(seq) : i # j => seq[i] # seq[j]

\* Calculate total stake in the system (Σ_all v ρ_v)
TotalStake == 
    LET vals == DOMAIN StakeMap
        seq == EnumerateSet(vals)
        n == Len(seq)
        folds == {f \in [0..n -> Nat] :
                      f[0] = 0 /\
                      \A i \in 1..n : f[i] = f[i - 1] + StakeMap[seq[i]]}
        totals == {f[n] : f \in folds}
    IN IF totals = {} THEN 0 ELSE CHOOSE total \in totals : TRUE

\* Calculate stake for a set of validators (Σ_{v ∈ set} ρ_v)
CalculateStake(validatorSet) ==
    LET vals == validatorSet \cap DOMAIN StakeMap
        seq == EnumerateSet(vals)
        n == Len(seq)
        folds == {f \in [0..n -> Nat] :
                      f[0] = 0 /\
                      \A i \in 1..n : f[i] = f[i - 1] + StakeMap[seq[i]]}
        totals == {f[n] : f \in folds}
    IN IF totals = {} THEN 0 ELSE CHOOSE total \in totals : TRUE

\* Get unique validators from a set of votes (enforce Def. 12 “count once”)
UniqueValidators(votes) ==
    {v.validator : v \in votes}

\* Calculate total stake from votes (counting each validator once!)
StakeFromVotes(votes) ==
    CalculateStake(UniqueValidators(votes))

\* Check if stake meets a percentage threshold (Σ ≥ θ% · Σ_total; Table 6)
MeetsThreshold(stake, thresholdPercent) ==
    stake * 100 >= TotalStake * thresholdPercent

\* ============================================================================
\* CERTIFICATE CREATION CONDITIONS
\* These functions check if we have enough votes to create certificates
\* ============================================================================

(***************************************************************************
 * READABILITY HELPER: Common vote scoping pattern
 * Filters a vote set to those for a particular (slot, blockHash) and
 * within a given set of vote types. Mirrors Table 6 rows (§2.4).
 ***************************************************************************)
VotesFor(votes, slot, blockHash, types) ==
    {v \in votes :
        /\ v.slot = slot
        /\ v.blockHash = blockHash
        /\ v.type \in types}

(***************************************************************************
 * PRECONDITION (documentation)
 * - The `votes` argument to the `CanCreate*` predicates is intended to be
 *   Pool-sourced (Definition 12, §2.5), e.g., `GetVotesForSlot(pool, s)`.
 * - Pool’s storage rules ensure at-most-once initial votes per validator per
 *   slot and bounded fallback votes (Def. 12). We still deduplicate by
 *   validator here (StakeFromVotes) for robustness and clarity.
 * - Once a threshold is met, Pool constructs and stores the certificate
 *   (Definition 13, §2.5) and broadcasts it.
 ***************************************************************************)

(***************************************************************************
 * Fast-Finalization Certificate (Table 6, row 1; §2.4)
 * - Vote type: NotarVote only
 * - Threshold: ≥80% of total stake
 * - Effect: Immediate finalization in one round (Definition 14, §2.5; and
 *   §2.6’s single-round path when ≥80% participate).
 ***************************************************************************)
\* PRECONDITION: `votes` is Pool-sourced (e.g., `GetVotesForSlot`) to respect
\* multiplicity rules; `StakeFromVotes` will still deduplicate by validator.
CanCreateFastFinalizationCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes : 
        /\ v.type = "NotarVote"
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), FastFinalThreshold)

(***************************************************************************
 * Notarization Certificate (Table 6, row 2; §2.4)
 * - Vote type: NotarVote only
 * - Threshold: ≥60% of total stake
 * - Effect: Block is notarized, enabling second-round FinalVote issuance.
 *   This is the first step of the slow path (§2.4, §2.6).
 ***************************************************************************)
CanCreateNotarizationCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes :
        /\ v.type = "NotarVote"
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

(***************************************************************************
 * Notar-Fallback Certificate (Table 6, row 3; §2.4–§2.5)
 * - Vote types: NotarVote OR NotarFallbackVote (mixed OK!)
 * - Threshold: ≥60% of total stake
 * - Effect: Fallback notarization used when initial votes are insufficient
 *   or delayed; emitted after SafeToNotar (§2.5, Definition 16) conditions.
 * - Count-once (Def. 12): stake is counted once per validator via
 *   UniqueValidators → StakeFromVotes, even if both NotarVote and
 *   NotarFallbackVote from the same validator are present.
 ***************************************************************************)
CanCreateNotarFallbackCert(votes, slot, blockHash) ==
    LET relevantVotes == VotesFor(votes, slot, blockHash,
                                  {"NotarVote", "NotarFallbackVote"})
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

(***************************************************************************
 * Skip Certificate (Table 6, row 4; §2.4–§2.5)
 * - Vote types: SkipVote OR SkipFallbackVote (mixed OK!)
 * - Threshold: ≥60% of total stake
 * - Effect: Slot is skipped (move on). SkipFallbackVote is emitted after
 *   SafeToSkip (§2.5, Definition 16) indicates no block can be fast-finalized.
 ***************************************************************************)
CanCreateSkipCert(votes, slot) ==
    LET relevantVotes == {v \in votes :
        /\ IsSkipVote(v)
        /\ v.slot = slot}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

(***************************************************************************
 * Finalization Certificate (Table 6, row 5; §2.4–§2.6)
 * - Vote type: FinalVote only
 * - Threshold: ≥60% of total stake
 * - Effect: Completes the slow path (two rounds). Finalizes the unique
 *   notarized block in that slot (Definition 14, §2.5).
 ***************************************************************************)
CanCreateFinalizationCert(votes, slot) ==
    LET relevantVotes == {v \in votes :
        /\ v.type = "FinalVote"
        /\ v.slot = slot}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

\* ============================================================================
\* CERTIFICATE CREATION FUNCTIONS
\* These actually create certificate objects when thresholds are met
\* ============================================================================

\* Canonicalize skip votes so the certificate carries at most one vote
\* per validator for the given slot (Def. 12: count-once; Def. 13: Pool
\* generates a single certificate per type). If both SkipVote and
\* SkipFallbackVote exist for a validator, prefer the SkipFallbackVote,
\* which is produced after SafeToSkip (§2.5, Def. 16) and reflects a
\* stricter condition.
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
    \* Note: `votes` is expected to be Pool-sourced (Def. 12, §2.5).
    \* Count-once semantics hold in practice; we still deduplicate on validation.
    [type |-> "NotarFallbackCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type \in {"NotarVote", "NotarFallbackVote"} /\ 
        v.slot = slot /\ v.blockHash = blockHash}]

\* PRECONDITIONS (documentation):
\* - votes \subseteq Vote; slot \in Slots (Messages.tla typing);
\* - Pool/GetVotesForSlot ensures these (Def. 12, §2.5).
CreateSkipCert(votes, slot) ==
    [type |-> "SkipCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> CanonicalizeSkipVotes(votes, slot)]

\* Note (Definition 14, §2.5): slow-path finalization is slot-scoped; the
\* finalized block is the unique notarized block in this slot. Hence
\* `blockHash = NoBlock`.
CreateFinalizationCert(votes, slot) ==
    [type |-> "FinalizationCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> {v \in votes : 
        v.type = "FinalVote" /\ v.slot = slot}]

\* ============================================================================
\* CERTIFICATE VALIDATION
\* ============================================================================

\* Check if a certificate is valid (Table 6 thresholds with relevance
\* filtering; §2.4; Pool §2.5). Compute Σ from exactly the votes relevant to
\* (type, slot, blockHash). We defensively check vote well-formedness per
\* Messages.tla. Conceptually, a real system would verify aggregate
\* signatures (§1.6) for the same message; here we reason at the set level.
IsValidCertificate(cert) ==
    LET RelevantVotes ==
            CASE cert.type = "FastFinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarFallbackCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote", "NotarFallbackVote"})
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

\* Optional: structural well-formedness of a certificate's vote contents.
\* This does not affect acceptance via IsValidCertificate, but is useful as an
\* invariant on Pool storage (one certificate per type for a given block/slot;
\* §2.5, Def. 13).
CertificateWellFormed(cert) ==
    LET RelevantVotes ==
            CASE cert.type = "FastFinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarFallbackCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote", "NotarFallbackVote"})
               [] cert.type = "SkipCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"SkipVote", "SkipFallbackVote"})
               [] cert.type = "FinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"FinalVote"})
               [] OTHER -> {}
    IN cert.votes \subseteq RelevantVotes

\* ============================================================================
\* CERTIFICATE PROPERTIES AND IMPLICATIONS
\* ============================================================================

(***************************************************************************
 * IMPORTANT IMPLICATION (whitepaper §2.4–§2.5):
 * - Table 6 thresholds imply that if a node can construct the
 *   Fast-Finalization Certificate (80%), it can also construct the
 *   Notarization Certificate (60%). The paper states this explicitly in §2.5
 *   (“fast ⇒ notar ⇒ fallback”).
 * Scope/assumption: The subset relation captures what a single node’s Pool
 * would produce from a consistent local view in slot s. Different nodes may
 * include different concrete vote sets due to timing, but thresholds coexist.
 ***************************************************************************)
FastFinalizationImpliesNotarization(fastCert, notarCert) ==
    /\ fastCert.type = "FastFinalizationCert"
    /\ notarCert.type = "NotarizationCert"
    /\ fastCert.slot = notarCert.slot
    /\ fastCert.blockHash = notarCert.blockHash
    => notarCert.votes \subseteq fastCert.votes

(***************************************************************************
 * IMPLICATION (cascade): Notarization implies Notar-Fallback (Table 6; §2.5)
 * If a NotarizationCert exists for (slot, block), the NotarFallbackCert for
 * the same (slot, block) is also constructible (60% threshold holds either way).
 ***************************************************************************)
NotarizationImpliesFallback(notarCert, fallbackCert) ==
    /\ notarCert.type = "NotarizationCert"
    /\ fallbackCert.type = "NotarFallbackCert"
    /\ notarCert.slot = fallbackCert.slot
    /\ notarCert.blockHash = fallbackCert.blockHash

(***************************************************************************
 * SANITY PROPERTY: Fast path excludes fallback votes.
 * Enforced by constructors; IsValidCertificate computes stake from the
 * relevant NotarVote subset, ignoring any extraneous votes.
 ***************************************************************************)
FastFinalizationVotesAreNotar(cert) ==
    cert.type = "FastFinalizationCert" =>
    \A v \in cert.votes : v.type = "NotarVote"

(***************************************************************************
 * LEMMA (documentation): Constructor validity under guard.
 * If the Notar-Fallback guard holds for (votes, s, b), then creating the
 * certificate with those votes yields a valid certificate. This matches
 * Pool behavior (§2.5, Def. 13) when thresholds are met.
 ***************************************************************************)
FallbackConstructorValidUnderGuard(votes, s, b) ==
    CanCreateNotarFallbackCert(votes, s, b)
        => IsValidCertificate(CreateNotarFallbackCert(votes, s, b))

(***************************************************************************
 * LEMMA (readability): Notarization guard implies Notar-Fallback guard.
 * Matches the paper’s implication chain (80% ⇒ 60% notar ⇒ 60% fallback;
 * §2.4–§2.5).
 ***************************************************************************)
NotarizationGuardImpliesFallbackGuard(votes, s, b) ==
    CanCreateNotarizationCert(votes, s, b)
        => CanCreateNotarFallbackCert(votes, s, b)

\* Check if two certificates conflict (shouldn't happen!)
\* Note: This predicate treats conflicts only within the same certificate type.
\* Cross-type coherence (e.g., Notarization vs NotarFallback for a slot)
\* is enforced by Pool storage rules and system invariants elsewhere.
\* Whitepaper anchors: §2.5 Def. 13 (one certificate per type per block/slot)
\* and Def. 14 (unique notarized block per slot for slow finalization).
ConflictingCertificates(cert1, cert2) ==
    /\ cert1.slot = cert2.slot           \* Same slot
    /\ cert1.type = cert2.type           \* Same type
    /\ cert1.blockHash # cert2.blockHash \* Different blocks!

\* Companion predicate (for use outside Pool if needed):
\* Detect cross-type conflicts among notar-related certificate types for the
\* same slot. Within Pool, CanStoreCertificate already forbids such states by
\* requiring a single blockHash across Notarization/NotarFallback/FastFinalization
\* for a slot (Pool §2.5; Def. 13).
CrossTypeNotarConflict(c1, c2) ==
    LET NotarTypes == {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}
    IN /\ c1.slot = c2.slot
       /\ c1.type \in NotarTypes
       /\ c2.type \in NotarTypes
       /\ c1.blockHash # c2.blockHash

\* ============================================================================
\* INVARIANTS FOR VERIFICATION
\* ============================================================================

\* All certificates must be valid (Table 6; §2.4; Pool §2.5)
\* Intended domain: apply to Pool’s certificates[slot] sets.
AllCertificatesValid(certificates) ==
    \A cert \in certificates : IsValidCertificate(cert)

\* No conflicting certificates should exist (Pool §2.5; Def. 13–14)
\* Intended domain: apply to Pool’s certificates[slot] sets.
NoConflictingCertificates(certificates) ==
    \A cert1, cert2 \in certificates :
        ~ConflictingCertificates(cert1, cert2)

\* Fast finalization implies a corresponding notarization with vote inclusion
\* (Table 6 thresholds; §2.5 “fast ⇒ notar ⇒ fallback”). Intended domain:
\* apply to Pool’s certificates[slot] sets.
FastPathImplication(certificates) ==
    \A fastCert \in certificates :
        fastCert.type = "FastFinalizationCert" =>
        \E notarCert \in certificates :
            FastFinalizationImpliesNotarization(fastCert, notarCert)

\* Notarization cascade: every notarization implies a corresponding fallback
NotarizationCascadeImplication(certificates) ==
    \A notarCert \in certificates :
        notarCert.type = "NotarizationCert" =>
        \E fallbackCert \in certificates :
            NotarizationImpliesFallback(notarCert, fallbackCert)

\* Skip vs Block-certificate mutual exclusion (per whitepaper intent):
\* No slot’s certificate set may contain both a SkipCert and any
\* block-related certificate (Notarization, NotarFallback, FastFinalization).
\* Rationale: A slot is either skipped, or (some block is) notarized; §2.6.
SkipVsBlockCertExclusion(certificates) ==
    LET hasSkip == \E c \in certificates : c.type = "SkipCert"
        hasBlock == \E c \in certificates :
                        c.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}
    IN ~(hasSkip /\ hasBlock)

\* Optional helper: all certificates in a set are structurally well-formed
AllCertificatesWellFormed(certificates) ==
    \A cert \in certificates : CertificateWellFormed(cert)

=============================================================================
