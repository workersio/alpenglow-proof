---------------------------- MODULE Messages ----------------------------

EXTENDS Naturals, FiniteSets

(***************************************************************************
 * Messaging layer — votes & certificates used by Votor
 *
 * Grounding (Alpenglow v1.1):
 *   • Vote and certificate message shapes: Table 5 & Table 6 (Def. 11).
 *   • Pool storage rules (e.g., up to 3 notar-fallback votes) & certificate creation/broadcast: Def. 12–13.
 *   • Slots & leaders: epoch iterates through s = 1..L; leader(s) known before epoch; slot is a natural number.
 *   • Validators (nodes) & signatures: nodes/validators, public keys; votes signed by node v.
 ***************************************************************************)

CONSTANTS
    Validators,     \* Nodes/validators for the epoch; each has a public key/stake.
    Slots,          \* Natural-numbered slots; epoch iterates s = 1..L.
    BlockHashes,    \* Abstract identifiers referenced by votes/certs as hash(b).
    NoBlock         \* Modeling sentinel for slot-only messages (Skip/Final carry no hash).

ASSUME
    /\ Validators # {}                 \* Non-empty validator set
    /\ Slots \subseteq Nat             \* “Slot … is a natural number.”
    /\ Slots # {}                      \* Non-empty slot set
    /\ \A s \in Slots : 1..s \subseteq Slots  \* Epoch iterates s = 1..L ⇒ prefix-closed.
    /\ BlockHashes # {}                \* Non-empty block-id universe
    /\ NoBlock \notin BlockHashes      \* Slot-only objects don’t include a block hash.

(***************************************************************************
 * Vote types — exactly the five from Table 5 (Def. 11)
 * Each object is signed by node v.
 ***************************************************************************)
VoteType == {
    "NotarVote",           \* NotarVote(slot(b), hash(b)) 
    "NotarFallbackVote",   \* NotarFallbackVote(slot(b), hash(b)) 
    "SkipVote",            \* SkipVote(s) 
    "SkipFallbackVote",    \* SkipFallbackVote(s) 
    "FinalVote"            \* FinalVote(s) 
}

NotarVoteT == "NotarVote"
NotarFallbackVoteT == "NotarFallbackVote"
SkipVoteT == "SkipVote"
SkipFallbackVoteT == "SkipFallbackVote"
FinalVoteT == "FinalVote"

(***************************************************************************
 * Vote record — field shapes mirror Table 5
 * Notar*/NotarFallback include hash(b); Skip*/Final are slot-only.
 * Message-size Table 11 also shows presence/absence of the block-hash field.
 ***************************************************************************)
Vote == [
    type: VoteType,
    validator: Validators,                    \* Signer is a node/validator.
    slot: Slots,                              \* Slot-scoped.
    blockHash: BlockHashes \cup {NoBlock}     \* NoBlock used for slot-only votes (Skip/Final).
]

(*******************************************************************************
 * Certificate types & structure — thresholds and scope (Table 6; Defs. 12–14)
 *   • FastFinalizationCert: NotarVote with Σ ≥ 80%  \n
 *   • NotarizationCert:     NotarVote with Σ ≥ 60%  \n
 *   • NotarFallbackCert:    {NotarVote, NotarFallbackVote} with Σ ≥ 60%  \n
 *   • SkipCert:             {SkipVote, SkipFallbackVote} with Σ ≥ 60%  \n
 *   • FinalizationCert:     FinalVote with Σ ≥ 60%                      \n
 * Σ = cumulative stake of aggregated votes.
 * Pool generates/broadcasts a certificate once thresholds are met and keeps one per type
 * per block/slot. (Def. 12–13; finalization semantics in Def. 14.)
 *******************************************************************************)

CreateNotarVote(validator, slot, blockHash) ==
    [type |-> NotarVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

CreateNotarFallbackVote(validator, slot, blockHash) ==
    [type |-> NotarFallbackVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

CreateSkipVote(validator, slot) ==
    [type |-> SkipVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]

CreateSkipFallbackVote(validator, slot) ==
    [type |-> SkipFallbackVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]

CreateFinalVote(validator, slot) ==
    [type |-> FinalVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]

(***************************************************************************
 * Vote classification helpers — shapes from Table 5
 ***************************************************************************)
IsNotarVote(vote) ==
    vote.type \in {NotarVoteT, NotarFallbackVoteT}

IsSkipVote(vote) ==
    vote.type \in {SkipVoteT, SkipFallbackVoteT}

IsFinalVote(vote) ==
    vote.type = FinalVoteT

IsInitialVote(vote) ==
    vote.type \in {NotarVoteT, SkipVoteT}

IsInitialNotarVote(vote) == vote.type = NotarVoteT

IsVoteForBlock(vote, blockHash) ==
    /\ IsNotarVote(vote)
    /\ vote.blockHash = blockHash

(***************************************************************************
 * Certificate record — aggregated votes forming certs (Table 6; Def. 13–14)
 * Block-scoped certs (carry hash(b)): FastFinalization, Notarization, NotarFallback. Slot-scoped:
 * SkipCert, FinalizationCert.
 ***************************************************************************)
CertificateType == {
    "FastFinalizationCert",
    "NotarizationCert",
    "NotarFallbackCert",
    "SkipCert",
    "FinalizationCert"
}

Certificate == [
    type: CertificateType,
    slot: Slots,
    blockHash: BlockHashes \cup {NoBlock},    \* NoBlock for slot-scoped certs (Skip/Final).
    votes: SUBSET Vote                        \* Aggregated votes per Table 6.
]

(*******************************************************************************
 * IsValidVote — structural well-formedness of votes (maps Table 5 to fields)
 * • Types & shapes: Notar*/NotarFallback(slot, hash(b)); Skip*/Final(slot only).
 * • Signer ∈ Validators (nodes/validators).
 * • Slots are naturals; epoch iterates 1..L.
 * • Message-size table also reflects presence/absence of hash field.
 *******************************************************************************)
IsValidVote(vote) ==
    /\ vote.type \in VoteType
    /\ vote.validator \in Validators
    /\ vote.slot \in Slots
    /\ (IsNotarVote(vote) => vote.blockHash \in BlockHashes)
    /\ (IsSkipVote(vote) \/ IsFinalVote(vote) => vote.blockHash = NoBlock)

=============================================================================
