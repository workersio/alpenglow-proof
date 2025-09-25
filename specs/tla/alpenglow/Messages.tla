---------------------------- MODULE Messages ----------------------------
(***************************************************************************
 * MESSAGE TYPES FOR ALPENGLOW CONSENSUS PROTOCOL
 *
 * Votor exchanges a small family of messages described in Whitepaper §2.4
 * (Definition 11, Tables 5–6). This file encodes them explicitly so later
 * modules can reason about which path (fast ≥80% or slow ≥60%) is active.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets

\* ============================================================================
\* CONSTANTS
\* ============================================================================

CONSTANTS
    Validators,     \* Set of all validator nodes in the network
    Slots,          \* Natural numbers representing time slots
    BlockHashes,    \* Set of possible block identifiers
    NoBlock         \* Special value meaning "no block" (for skip votes)

\* Basic assumptions about our constants
ASSUME
    /\ Validators # {}           \* At least one validator exists
    /\ Slots \subseteq Nat       \* Slots are natural numbers
    /\ \A s \in Slots : 0..s \subseteq Slots  \* Prefix-closed domain for slot arithmetic
    /\ BlockHashes # {}          \* At least one possible block hash
    /\ NoBlock \notin BlockHashes \* NoBlock is distinct from real blocks

\* ============================================================================
\* VOTE TYPES (Definition 11, Table 5 from whitepaper)
\* ============================================================================

(***************************************************************************
 * The five vote types in Alpenglow:
 * 
 * 1. NotarVote: "I approve this block" (first vote)
 * 2. NotarFallbackVote: "Others seem to approve, I'll go along" (safety vote)
 * 3. SkipVote: "This slot timed out, skip it" (first skip)
 * 4. SkipFallbackVote: "Others want to skip, I'll go along" (safety skip)
 * 5. FinalVote: "This block was notarized, finalize it" (second round)
 ***************************************************************************)

VoteType == {
    "NotarVote",           \* Initial approval vote for a block
    "NotarFallbackVote",   \* Fallback approval (up to 3 allowed per validator)
    "SkipVote",            \* Initial vote to skip a slot
    "SkipFallbackVote",    \* Fallback skip vote
    "FinalVote"            \* Second-round finalization vote
}

\* Structure of a vote message
Vote == [
    type: VoteType,                           \* Which of the 5 vote types
    validator: Validators,                    \* Who is voting
    slot: Slots,                             \* Which slot this vote is for
    blockHash: BlockHashes \union {NoBlock}  \* What block (NoBlock for skips)
]

\* ============================================================================
\* VOTE CREATION HELPERS
\* These functions create properly formatted vote messages
\* ============================================================================

(***************************************************************************
 * Abstraction note on signatures
 * - The whitepaper describes votes and certificates as signed messages and
 *   aggregated signatures. In this model, we abstract signatures as sets of
 *   votes with stake-weighted aggregation performed by StakeFromVotes
 *   (see Certificates.tla). There are no explicit cryptographic artifacts
 *   here; only the logical content and stake thresholds matter for safety.
 ***************************************************************************)

\* Definition 11 (Table 5): NotarVote — validator immediately approves
\* block `blockHash` for slot `slot`.
CreateNotarVote(validator, slot, blockHash) ==
    [type |-> "NotarVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

\* Definition 11: NotarFallbackVote — emitted after SafeToNotar to back
\* the same block once enough peers voted.
\* Note: signatures are abstracted; this records logical content only.
CreateNotarFallbackVote(validator, slot, blockHash) ==
    [type |-> "NotarFallbackVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

\* Definition 11: SkipVote — initial vote to skip the slot (no block hash).
\* Whitepaper Table 5: skip votes carry no block reference; we encode this by
\* setting `blockHash = NoBlock` and enforce it via IsValidVote.
CreateSkipVote(validator, slot) ==
    [type |-> "SkipVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]  \* Skip votes don't reference a block

\* Definition 11: SkipFallbackVote — broadcast after SafeToSkip confirms
\* the slot cannot be notarized.
\* Whitepaper refs: Algorithm 1 (lines 21–25) issues SkipFallbackVote(s)
\* after attempting to skip unvoted slots; Definition 16 (Fallback events)
\* specifies the SafeToSkip preconditions that gate this emission.
CreateSkipFallbackVote(validator, slot) ==
    [type |-> "SkipFallbackVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]

\* Definition 11: FinalVote — second round of voting used in the 60% path.
\* Whitepaper refs: Algorithm 2 (TRYFINAL, lines 18–21) and Definition 14
\* (slot-scoped finalization). We encode slot scoping by setting
\* `blockHash |-> NoBlock` so FinalVote(s) carries only the slot.
CreateFinalVote(validator, slot) ==
    [type |-> "FinalVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]  \* Slot-scoped finalization vote (FinalVote(s))

\* Optional typed wrapper (audit suggestion): documents intent that callers
\* pass a slot and returns the correctly shaped skip vote.
CreateSkipVoteForSlot(v, s) == CreateSkipVote(v, s)

\* ============================================================================
\* VOTE CLASSIFICATION HELPERS
\* These help categorize and query votes
\* ============================================================================

\* Helper predicates mirror terminology in §2.4 so other modules can test
\* for "approval" vs "skip" votes.

\* Does this vote approve a block (either initial or fallback)?
\* Alias note: "IsApprovalVote" is the preferred name (audit suggestion)
\* to avoid confusion with "initial notarization"; keep both for clarity.
IsNotarVote(vote) ==
    vote.type \in {"NotarVote", "NotarFallbackVote"}
IsApprovalVote(vote) == IsNotarVote(vote)

\* Does this vote skip the slot (initial or fallback)?
IsSkipVote(vote) ==
    vote.type \in {"SkipVote", "SkipFallbackVote"}

\* Is this a finalization vote?
IsFinalVote(vote) ==
    vote.type = "FinalVote"

\* Initial votes are the ones counted once per slot (Definition 12 / Lemma 20).
IsInitialVote(vote) ==
    vote.type \in {"NotarVote", "SkipVote"}

\* Is this a fallback vote (safety mechanism)?
IsFallbackVote(vote) ==
    vote.type \in {"NotarFallbackVote", "SkipFallbackVote"}

\* Does this vote support a specific block?
IsVoteForBlock(vote, blockHash) ==
    /\ IsApprovalVote(vote)
    /\ vote.blockHash = blockHash

\* (lemmas moved below IsValidVote for parser ordering)

\* ============================================================================
\* CERTIFICATE TYPES (Definition 11, Table 6 from whitepaper)
\* ============================================================================

(***************************************************************************
 * Certificates are aggregated votes that meet the stake thresholds from
 * Whitepaper Table 6. Each constructor below corresponds to one row of the
 * table (fast ≥80%, all others ≥60%).
 ***************************************************************************)

CertificateType == {
    "FastFinalizationCert",  \* 80% threshold - one round finalization!
    "NotarizationCert",      \* 60% threshold - enables second round
    "NotarFallbackCert",     \* 60% threshold - mixed vote types OK
    "SkipCert",              \* 60% threshold - skip this slot
    "FinalizationCert"       \* 60% threshold - complete slow path
}

\* Structure of a certificate
\* Note: NoBlock is intentional for slot-scoped certificates (Skip/Finalization).
\* Relevance filtering of `votes` by (type, slot, blockHash) happens during
\* validation; see `Certificates.tla` → `IsValidCertificate` and
\* `CertificateWellFormed` for details.
Certificate == [
    type: CertificateType,                    \* Which certificate type
    slot: Slots,                              \* Which slot
    blockHash: BlockHashes \union {NoBlock},  \* Which block (or NoBlock)
    votes: SUBSET Vote                        \* The votes in this certificate
]

\* ============================================================================
\* VOTE VALIDATION
\* ============================================================================

\* Check if a vote is properly formatted and valid
IsValidVote(vote) ==
    /\ vote.type \in VoteType
    /\ vote.validator \in Validators
    /\ vote.slot \in Slots
    /\ (IsNotarVote(vote) => vote.blockHash \in BlockHashes)
    /\ (IsSkipVote(vote) \/ IsFinalVote(vote) => vote.blockHash = NoBlock)

\* ============================================================================
\* DOMAIN LEMMAS (audit suggestion)
\* Make explicit the blockHash domain by vote family, already enforced by
\* IsValidVote; these theorems document intended shapes for proof clarity.
\* ============================================================================

THEOREM ApprovalVotesCarryBlockHash ==
    \A v \in Vote :
        (IsValidVote(v) /\ IsApprovalVote(v)) => v.blockHash \in BlockHashes

THEOREM NonBlockVotesUseNoBlock ==
    \A v \in Vote :
        (IsValidVote(v) /\ (IsSkipVote(v) \/ IsFinalVote(v))) => v.blockHash = NoBlock

\* Audit lemma (creation-time validity): Any SkipFallbackVote constructed by
\* the helper is a valid vote per IsValidVote typing/shape rules.
THEOREM SkipFallbackVoteCreationIsValid ==
    \A v \in Validators, s \in Slots :
        IsValidVote(CreateSkipFallbackVote(v, s))

\* Audit lemma (creation-time validity): Any SkipVote constructed by the
\* helper is a valid vote per IsValidVote typing/shape rules.
THEOREM SkipVoteCreationIsValid ==
    \A v \in Validators, s \in Slots :
        IsValidVote(CreateSkipVote(v, s))

\* Check if two votes conflict (violate protocol rules)
\* Captures any double initial voting per slot by a validator
\* (Whitepaper Def. 12 and Lemma 20).
ConflictingVotes(vote1, vote2) ==
    /\ vote1.validator = vote2.validator
    /\ vote1.slot = vote2.slot
    /\ IsInitialVote(vote1)
    /\ IsInitialVote(vote2)
    /\ vote1 # vote2

\* ============================================================================
\* QUERY FUNCTIONS
\* These help analyze sets of votes
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

\* Get all votes supporting a specific block
GetVotesForBlock(votes, slot, blockHash) ==
    {v \in votes : 
        /\ v.slot = slot
        /\ IsVoteForBlock(v, blockHash)}

=============================================================================
