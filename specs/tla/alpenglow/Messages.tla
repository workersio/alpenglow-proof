---------------------------- MODULE Messages ----------------------------
(***************************************************************************
 * MESSAGE TYPES FOR ALPENGLOW (Votes & Certificates)
 *
 * What this module specifies and where it comes from in the whitepaper:
 *   • §2.4 (Def. 11; :478) — the five vote messages (Table 5 :497) and the
 *     five certificate messages (Table 6 :507). These encode the “fast ≥80%”
 *     and “slow ≥60% + second round” finalization paths referenced across the
 *     protocol (§1.5 latency intuition; §2.6 algorithms).
 *   • §2.5 (Defs. 12–15; :513, :520, :536, :543) — Pool rules (store-once
 *     per slot per validator for initial votes; bounded fallbacks), generated
 *     certificates, and the BlockNotarized/ParentReady events that gate voting.
 *   • §1.6 (Aggregate Signature; :263) — certificates are aggregated votes.
 *
 * Modeling notes and rationale used by Blocks/VoteStorage/Certificates:
 *   • Slot-only messages. SkipVote(s), SkipFallbackVote(s), and FinalVote(s)
 *     are slot-scoped (Table 5 :497). We model this by carrying `blockHash =
 *     NoBlock` for those types and prove shape lemmas below. This keeps the
 *     domain of `blockHash` disjoint from real block hashes to avoid type
 *     confusion across modules.
 *   • Content-only signatures. The paper signs messages and aggregates
 *     signatures into certificates. Here, signatures are abstracted away; we
 *     model only the logical content and compute stake Σ over validators when
 *     constructing certificates (see Certificates.tla and §1.6 :263).
 *   • Initial vs. fallback votes. “Initial” votes are NotarVote and SkipVote
 *     (Def. 12 :513, Lemma 20 :820 — at most one per slot/validator). Fallback
 *     votes (NotarFallbackVote, SkipFallbackVote) are emitted after SafeToNotar
 *     or SafeToSkip (Def. 16 :554) and do not change the “count once” rule for
 *     stake (Pool enforces multiplicity; VoteStorage.tla).
 *
 * Cross-links:
 *   • Blocks.tla consumes these types only indirectly (via ParentReady and
 *     finality semantics in §2.5) but benefits from the clear slot/block
 *     scoping encoded here when reasoning about ancestry and single-chain.
 *   • Certificates.tla implements the Table 6 threshold checks over these
 *     messages and their Σ stake contributions.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets

\* ============================================================================
\* CONSTANTS (whitepaper mapping: §2.4, §2.5)
\* ============================================================================

CONSTANTS
    Validators,     \* All validators (stake-weighted in §2.4/§2.5)
    Slots,          \* Natural-numbered slots (§2.4 context; ordered timeline)
    BlockHashes,    \* Abstract block identifiers (cf. Blocks.tla §2.1)
    NoBlock         \* Sentinel for slot-only messages (Table 5 :497)

\* Basic assumptions about our constants
ASSUME
    /\ Validators # {}                 \* Non-empty validator set
    /\ Slots \subseteq Nat             \* Slots are naturals
    /\ \A s \in Slots : 0..s \subseteq Slots  \* Prefix-closed slot domain
    /\ BlockHashes # {}                \* Non-empty block-id universe
    /\ NoBlock \notin BlockHashes      \* Slot-only objects can’t be blocks

\* ============================================================================
\* VOTE TYPES (Whitepaper §2.4, Definition 11; Table 5 :497)
\* ============================================================================

(***************************************************************************
 * The five vote messages (Table 5 :497):
 * 1) NotarVote(slot(b), hash(b)) — initial approval for block b
 * 2) NotarFallbackVote(slot(b), hash(b)) — fallback approval after SafeToNotar
 * 3) SkipVote(s) — initial decision to skip slot s
 * 4) SkipFallbackVote(s) — fallback decision to skip after SafeToSkip
 * 5) FinalVote(s) — second-round finalization vote for slot s
 *
 * Reasoning and flow (§2.4–§2.6):
 * - Fast path (≥80%): enough NotarVote stake yields fast-finalization in one
 *   round (Table 6; Certificates). Slow path (≥60%): notarization enables
 *   FinalVote and then FinalizationCert (two rounds). Fallback votes are gated
 *   by Definition 16 (SafeToNotar/Skip) and do not permit double-initial votes
 *   (Lemma 20 :820; Pool multiplicity per Def. 12 :513).
 ***************************************************************************)

VoteType == {
    "NotarVote",           \* Initial approval vote for a block
    "NotarFallbackVote",   \* Fallback approval (up to 3 allowed per validator)
    "SkipVote",            \* Initial vote to skip a slot
    "SkipFallbackVote",    \* Fallback skip vote
    "FinalVote"            \* Second-round finalization vote
}

\* Optional symbolic names for vote tags (audit suggestion)
NotarVoteT == "NotarVote"
NotarFallbackVoteT == "NotarFallbackVote"
SkipVoteT == "SkipVote"
SkipFallbackVoteT == "SkipFallbackVote"
FinalVoteT == "FinalVote"

\* Structure of a vote message (shapes mirror Table 5 :497)
Vote == [
    type: VoteType,                           \* Which of the 5 vote types
    validator: Validators,                    \* Who is voting
    slot: Slots,                             \* Which slot this vote is for
    blockHash: BlockHashes \cup {NoBlock}  \* What block (NoBlock for skips)
]

\* ============================================================================
\* VOTE CREATION HELPERS (where they appear in Algorithms 1–2)
\* ============================================================================

(***************************************************************************
 * Signatures are abstracted (cf. §1.6 :263). These constructors create the
 * logical content that Algorithm 1/2 broadcast at specific lines:
 * - NotarVote: Alg. 2 line 12 (TRYNOTAR) when parent condition holds.
 * - SkipVote:  Alg. 2 line 25 (TRYSKIPWINDOW) for unvoted slots.
 * - NotarFallbackVote: Alg. 1 line 19 after SafeToNotar(s,h) (Def. 16 :554).
 * - SkipFallbackVote:  Alg. 1 line 24 after SafeToSkip(s) (Def. 16 :554).
 * - FinalVote: Alg. 2 line 20 (TRYFINAL) when notarized + own notar vote and
 *   BadWindow ∉ state (prevents mixing fallback with FinalVote; see :847–:849).
 ***************************************************************************)

\* Definition 11 (Table 5): NotarVote(slot(b), hash(b)) — initial approval.
CreateNotarVote(validator, slot, blockHash) ==
    [type |-> NotarVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

\* Definition 11: NotarFallbackVote(slot(b), hash(b)) — fallback approval.
\* Emitted after SafeToNotar (Def. 16 :554; Alg. 1 line 19).
CreateNotarFallbackVote(validator, slot, blockHash) ==
    [type |-> NotarFallbackVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

\* Definition 11: SkipVote(s) — initial skip (slot-only; Table 5 :497).
\* We encode slot-only by setting `blockHash = NoBlock` and enforce it in IsValidVote.
CreateSkipVote(validator, slot) ==
    [type |-> SkipVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]  \* Skip votes don't reference a block

\* Definition 11: SkipFallbackVote(s) — fallback skip after SafeToSkip.
\* Alg. 1 line 24; gated by Def. 16’s SafeToSkip condition (:554, :571).
CreateSkipFallbackVote(validator, slot) ==
    [type |-> SkipFallbackVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]

\* Definition 11: FinalVote(s) — second round in the ≥60% path (Table 6).
\* Alg. 2 line 20; Def. 14 (:536) says FinalizationCert(s) finalizes the
\* unique notarized block in s. Slot-only encoded via `blockHash = NoBlock`.
CreateFinalVote(validator, slot) ==
    [type |-> FinalVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]  \* Slot-scoped finalization vote (FinalVote(s))

\* Optional typed wrapper (ergonomics): documents intent to create SkipVote(s).
CreateSkipVoteForSlot(v, s) == CreateSkipVote(v, s)

\* ============================================================================
\* VOTE CLASSIFICATION HELPERS (terminology from §2.4/Def. 11)
\* ============================================================================

\* Helpers mirror the paper’s families: approval (notarization) vs skip, and
\* finalization. Used by Pool/Certificates to scope stake and enforce rules.

\* Does this vote approve a block (either initial or fallback)?
\* Alias note: "IsApprovalVote" is the preferred name (audit suggestion)
\* to avoid confusion with "initial notarization"; keep both for clarity.
IsNotarVote(vote) ==
    vote.type \in {NotarVoteT, NotarFallbackVoteT}
IsApprovalVote(vote) == IsNotarVote(vote)

\* Does this vote skip the slot (initial or fallback)?
IsSkipVote(vote) ==
    vote.type \in {SkipVoteT, SkipFallbackVoteT}

\* Is this a finalization vote?
IsFinalVote(vote) ==
    vote.type = FinalVoteT

\* Initial votes are the ones counted once per slot (Def. 12 :513; Lemma 20 :820).
IsInitialVote(vote) ==
    vote.type \in {NotarVoteT, SkipVoteT}

\* Convenience: explicit predicate for the initial notarization vote type.
IsInitialNotarVote(vote) ==
    vote.type = NotarVoteT

\* Is this a fallback vote (safety mechanism gated by Def. 16 :554)?
IsFallbackVote(vote) ==
    vote.type \in {"NotarFallbackVote", "SkipFallbackVote"}

\* Does this vote support a specific block? (Only approval votes have hashes.)
IsVoteForBlock(vote, blockHash) ==
    /\ IsApprovalVote(vote)
    /\ vote.blockHash = blockHash

\* (lemmas moved below IsValidVote for parser ordering)

\* ============================================================================
\* CERTIFICATE TYPES (Whitepaper §2.4, Definition 11; Table 6 :507)
\* ============================================================================

(***************************************************************************
 * Certificates aggregate votes that meet Table 6 thresholds (Σ stake):
 * - FastFinalizationCert — NotarVote, Σ ≥ 80% (one-round finality)
 * - NotarizationCert — NotarVote, Σ ≥ 60% (enables FinalVote)
 * - NotarFallbackCert — Notar/NotarFallback, Σ ≥ 60%
 * - SkipCert — Skip/SkipFallback, Σ ≥ 60%
 * - FinalizationCert — FinalVote, Σ ≥ 60% (completes slow path)
 * Aggregate signatures are abstracted (cf. §1.6 :263). Pool uniqueness and
 * “count once per slot” come from Definitions 12–13 (§2.5 :513, :520).
 ***************************************************************************)

CertificateType == {
    "FastFinalizationCert",  \* 80% threshold - one round finalization!
    "NotarizationCert",      \* 60% threshold - enables second round
    "NotarFallbackCert",     \* 60% threshold - mixed vote types OK
    "SkipCert",              \* 60% threshold - skip this slot
    "FinalizationCert"       \* 60% threshold - complete slow path
}

\* Structure of a certificate
\* - Slot-scoped certificates use NoBlock (Skip, Finalization; Table 6 :507).
\* - The `votes` bag is filtered/checked by Certificates.tla to include only
\*   relevant messages and to enforce Σ stake and well-formedness.
Certificate == [
    type: CertificateType,                    \* Which certificate type
    slot: Slots,                              \* Which slot
    blockHash: BlockHashes \cup {NoBlock},  \* Which block (or NoBlock)
    votes: SUBSET Vote                        \* The votes in this certificate
]

\* ============================================================================
\* VOTE VALIDATION (shapes follow Table 5 :497)
\* ============================================================================

\* Check that a vote is well-typed for its family:
\* - Approval votes carry a real block hash.
\* - Skip/Final votes are slot-only and must carry NoBlock.
IsValidVote(vote) ==
    /\ vote.type \in VoteType
    /\ vote.validator \in Validators
    /\ vote.slot \in Slots
    /\ (IsNotarVote(vote) => vote.blockHash \in BlockHashes)
    /\ (IsSkipVote(vote) \/ IsFinalVote(vote) => vote.blockHash = NoBlock)

\* ============================================================================
\* DOMAIN LEMMAS (document the intended shapes per Table 5)
\* ============================================================================

THEOREM ApprovalVotesCarryBlockHash ==
    \A v \in Vote :
        (IsValidVote(v) /\ IsApprovalVote(v)) => v.blockHash \in BlockHashes

THEOREM NonBlockVotesUseNoBlock ==
    \A v \in Vote :
        (IsValidVote(v) /\ (IsSkipVote(v) \/ IsFinalVote(v))) => v.blockHash = NoBlock

\* Creation-time validity: construction helpers respect IsValidVote shapes.
THEOREM SkipFallbackVoteCreationIsValid ==
    \A v \in Validators, s \in Slots :
        IsValidVote(CreateSkipFallbackVote(v, s))

THEOREM SkipVoteCreationIsValid ==
    \A v \in Validators, s \in Slots :
        IsValidVote(CreateSkipVote(v, s))

\* Check if two votes conflict (double-initial per slot/validator).
\* Mirrors Def. 12’s “store once” and Lemma 20 :820 (one initial vote/slot).
ConflictingVotes(vote1, vote2) ==
    /\ vote1.validator = vote2.validator
    /\ vote1.slot = vote2.slot
    /\ IsInitialVote(vote1)
    /\ IsInitialVote(vote2)
    /\ vote1 # vote2

\* ============================================================================
\* QUERY FUNCTIONS (used by Pool/Certificates)
\* ============================================================================

\* Get all votes of a specific type from a set
GetVotesByType(votes, voteType) ==
    {v \in votes : v.type = voteType}

\* Get all votes for a specific slot
GetVotesBySlot(votes, slot) ==
    {v \in votes : v.slot = slot}

\* Get all votes from a specific validator
GetVotesByValidator(votes, validator) ==
    {v \in votes : v.validator = validator}

\* Get all votes supporting a specific block (approval-only by shape)
GetVotesForBlock(votes, slot, blockHash) ==
    {v \in votes : 
        /\ v.slot = slot
        /\ IsVoteForBlock(v, blockHash)}

=============================================================================
