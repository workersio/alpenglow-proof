---------------------------- MODULE Blocks ----------------------------
(***************************************************************************
 * BLOCK STRUCTURE AND RELATIONSHIPS FOR ALPENGLOW
 *
 * What this module specifies and where it comes from in the whitepaper:
 *   • §1.1 (p. 3) — slots, designated leaders, public (VRF-based) schedule.
 *   • §2.1 (Def. 3–5; pp. 14–16) — block contents, block hash, ancestry.
 *   • §2.7 (and Alg. 3; pp. 26–27) — fixed-length leader windows and creation.
 *   • Correctness overview (p. 11) & Theorem 1 (p. 34) — single-chain finality.
 *
 * This file gives the core “data types” and helper predicates for blocks,
 * ancestry, and leader windows used by the higher-level protocol modules.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Messages, Sequences

\* ============================================================================
\* CONSTANTS (whitepaper mapping: §1.1, §2.1, §2.7)
\* ============================================================================

CONSTANTS
    GenesisHash,     \* Abstract hash of genesis (Def. 4; §2.1)
    WindowSize,      \* Fixed consecutive slots per leader window (§2.7)
    WindowLeader     \* Window-indexed leader map (VRF abstraction; §1.1)

ASSUME
    /\ GenesisHash \in BlockHashes
    /\ WindowSize \in Nat \ {0}

(* ------------------------------------------------------------------------------
 * Block Definition in Alpenglow — Control-Plane vs Data-Plane Abstraction
 * ------------------------------------------------------------------------------
 * In the *Solana Alpenglow Protocol* (v1.1 whitepaper):
 * 
 *   • A **block (b)** is formally defined as:
 *     "The sequence of all slices of a slot, for the purpose of voting and
 *     reaching consensus."  — Definition 3, §2.1 (Shred, Slice, Block) [p. 15]
 *     Each slice is itself a decoded data unit with its own Merkle root and
 *     leader signature.  (Definitions 1–2 [p. 14–15])
 * 
 *   • The **block hash**, `hash(b)`, is the Merkle-tree root over all slice roots
 *     `r₁ … rₖ`  — Definition 4 [p. 15–16].  
 *     The **slot** of a block, `slot(b)`, is the natural-number time slot `s`
 *     in which it was produced.
 * 
 *   • The **parent(b)** field links blocks into a chain/tree by referencing the
 *     hash of the previous block  — Definition 5 [p. 16].  
 *     The **leader** responsible for producing `b` is the validator assigned to
 *     that slot’s *leader window*  — §1.1 Alpenglow Overview [p. 3].
 * 
 * For reasoning about *safety*, *liveness*, and *leader-window handover*,
 * we abstract away the data-plane details (slices, shreds, Merkle paths)
 * and represent a block by its **control-plane metadata** only:
 * 
 *     Block = {
 *         slot   : Nat,          // time slot index — Definition 3
 *         hash   : Hash,         // Merkle root of slice roots — Definition 4
 *         parent : Hash,         // parent block reference — Definition 5
 *         leader : ValidatorID   // node producing this slot — §1.1
 *     }
 * 
 * Note on the leader field: The leader is derivable from leader(slot) and is
 * verified in the data plane by signature checks on slices (Definitions 1–2).
 * We include it explicitly here as a modeling convenience for predicates like
 * LeaderMatchesSchedule, rather than as a consensus-layer header field.
 * 
 * This abstraction is sufficient for formal proofs and protocol reasoning,
 * while the actual implementation additionally includes the slice/shred
 * hierarchy for data dissemination and repair (§2.1–§2.2).
 * 
 * References:
 *   • Solana Alpenglow White Paper v1.1 — §1.1 (p. 3), §2.1 (p. 14–16)
 *     [Definitions 1 – 5]
 * ------------------------------------------------------------------------------ *)

Block == [
    slot: Slots,
    hash: BlockHashes,
    parent: BlockHashes,
    leader: Validators
]

(* ------------------------------------------------------------------------------
 * GenesisBlock — Sentinel Origin of the Chain
 * ------------------------------------------------------------------------------
 * The Alpenglow whitepaper (§1.5, p. 11) introduces a *"notional genesis block"*
 * as the logical root of the blockchain. It is not a literal data structure in
 * the protocol but a conceptual anchor ensuring that every block has a parent.
 * 
 * Protocol slots are defined as s = 1, 2, ..., L (§1.1, p. 9). Genesis (slot 0)
 * is NOT a protocol slot but a sentinel for ancestry termination. When reasoning
 * about the protocol, quantifiers over Slots should range over s >= 1.
 * 
 * Rationale:
 *   • The genesis block provides a terminating base case for parent-link traversal.
 *   • Self-parenting (parent = hash) forms a clean sentinel so ancestry checks stop
 *     when reaching the root.
 *   • Genesis occurs before any leader window (§1.1, p. 3); the chosen validator is
 *     irrelevant for correctness.
 * 
 * Reference:
 *   • Solana Alpenglow White Paper v1.1 — §1.5 "Correctness" (p. 11)
 *     "Every block is associated with a parent (starting at some notional genesis block)..."
 *   • §1.1 (p. 9): "slots s = 1, 2, ..., L"
 * ------------------------------------------------------------------------------ *)

GenesisBlock == [
    slot |-> 0,
    hash |-> GenesisHash,
    parent |-> GenesisHash,  \* Self-parented sentinel for ancestry termination
    leader |-> CHOOSE v \in Validators : TRUE  \* Arbitrary; leader is irrelevant
]

IsGenesis(b) ==
    /\ b.slot = 0
    /\ b.hash = GenesisHash
    /\ b.parent = GenesisHash

(* ----------
 *
 *  A block is valid if:
 *  - Its slot number exists in the global set of Slots.
 *  - Its hash and parent are valid cryptographic block identifiers.
 *  - Its leader belongs to the current validator set.
 *  - It obeys the slot ordering rule — no non-genesis block may reference itself as parent.
 *  - The genesis block (slot = 0) is a unique self-parented sentinel anchoring the chain.
 *  
 *  Note: The parent-child slot ordering constraint (child.slot > parent.slot) is
 *  enforced by ValidParentChild, not here, since it requires both blocks.
 *  
 *  Grounded in:
 *  – Definition 3–5 (§2.1, pp. 14-16): slot(b), hash(b), parent(b)
 *  – §1.1 (p. 3) and §1.5 (p. 11): leader scheduling, parent-child chain, genesis reference
 *
 * ---------- *)
IsValidBlock(b) ==
    /\ b.slot \in Slots
    /\ b.hash \in BlockHashes
    /\ b.parent \in BlockHashes
    /\ b.leader \in Validators
    /\ b.slot > 0 => b.parent # b.hash
    /\ (b.slot = 0 => IsGenesis(b))

(* ------------------------------------------------------------------------------
 * ValidParentChild rationale (Alpenglow whitepaper)
 * 
 * Rationale for parent–child checks in Alpenglow
 * 
 * • Parent linkage by hash:
 *   The block’s data M includes both slot(parent(b)) and hash(parent(b)),
 *   meaning a child block carries its parent’s hash in its metadata.
 *   (p. 15, Definition 3)
 * 
 * • Protocol usage of the parent hash:
 *   Voting logic operates on the parent hash recorded in the block header:
 *   Block(s, hash, hash_parent) and ParentReady(hash_parent).
 *   (pp. 24–25, Algorithms 1–2)
 * 
 * • Strictly increasing slots:
 *   A child’s slot must be higher than its parent’s slot, enforcing
 *   forward time and forbidding “time-travel” links.
 *   (p. 11)
 * 
 * • Structural consequence:
 *   Parent pointers combined with strictly increasing slots imply
 *   edges always point to earlier slots (acyclic). When finalized,
 *   blocks form a single chain of parent references.
 *   (p. 22; see also the descendant-based safety phrasing on p. 11)
 *
 * ------------------------------------------------------------------------------ *)
ValidParentChild(parent, child) ==
    /\ parent.hash = child.parent   \* Child references parent correctly
    /\ parent.slot < child.slot     \* Parent comes before child

\* ============================================================================
\* VOTE HELPERS (block-typed wrappers)
\* ============================================================================

(***************************************************************************
 * Create a notarization vote for a given block. This wrapper preserves the
 * intended slot–hash pairing by construction and avoids accidental mismatch
 * at call sites.
 *
 * Note: This is a typed convenience; it relies on IsValidBlock(b) for
 * well-formedness, and on Messages.IsValidVote for vote validity checks.
 ***************************************************************************)
CreateNotarVoteForBlock(v, b) ==
    CreateNotarVote(v, b.slot, b.hash)


CreateNotarFallbackVoteForBlock(v, b) ==
    CreateNotarFallbackVote(v, b.slot, b.hash)

(* 
IsAncestor(b1, b2) — rationale from the Alpenglow whitepaper

• Ancestor ≙ reachability via parent links (reflexive):
  Definition 5 states an ancestor of block b is any block reachable from b by
  following parent links (b, parent(b), parent(parent(b)), …), and explicitly notes
  that b is its own ancestor (p. 15).

• Backward walk via parent identifiers in block data:
  Definition 3 specifies that each block’s data includes slot(parent(b)) and
  hash(parent(b)), enabling a search step that finds the unique parent by
  matching a block with hash == child.parent (p. 15).

• Termination conditions:
  The chain starts at “some notional genesis block”; thus, starting from b2 and
  repeatedly following parent links will either (i) encounter b1 (ancestor found),
  (ii) reach genesis without finding b1 (no ancestry), or (iii) hit a missing parent
  in the available set (broken chain ⇒ no ancestry). (p. 11)

References: p. 11 (genesis lineage), p. 15 (Def. 3: parent identifiers; Def. 5: ancestor/descendant).
*)
IsAncestor(b1, b2, allBlocks) ==
    LET
        ReachableFrom[b \in allBlocks] ==
            IF b = b1 THEN TRUE  \* Found the ancestor!
            ELSE IF b.hash = GenesisHash THEN (b1.hash = GenesisHash)  \* Hit genesis; check if b1 is genesis
            ELSE 
                \* Find the parent block and continue
                LET parentBlocks == {p \in allBlocks : p.hash = b.parent}
                IN IF parentBlocks = {} THEN FALSE
                   ELSE LET parent == CHOOSE p \in parentBlocks : TRUE
                        IN ReachableFrom[parent]
    IN b1 = b2 \/ ReachableFrom[b2]  \* A block is its own ancestor

(* 
GetAncestors / ComparableByAncestry — Alpenglow whitepaper grounding

• Ancestor/descendant relation:
  Defined as reachability via parent links (“b, parent(b), parent(parent(b)), …”).
  The relation is reflexive: a block is its own ancestor and descendant.
  Reference: p. 15, Definition 5.

• Parent linkage available in block data:
  Each block’s data M contains slot(parent(b)) and hash(parent(b)),
  enabling backward traversal by matching parent identifiers.
  Reference: p. 15, Definition 3.

• GetAncestors(b, allBlocks):
  The set { x ∈ allBlocks : IsAncestor(x, b) }.
  Due to reflexivity (Def. 5), this set includes b itself unless explicitly excluded.
  Reference: p. 15, Definition 5.

• ComparableByAncestry(b1, b2, allBlocks):
  TRUE iff IsAncestor(b1, b2) ∨ IsAncestor(b2, b1),
  i.e., the blocks are related by the ancestor/descendant relation.
  Reference: p. 15, Definition 5.
*)

GetAncestors(b, allBlocks) ==
    {ancestor \in allBlocks : IsAncestor(ancestor, b, allBlocks)}

ComparableByAncestry(b1, b2, allBlocks) ==
    IsAncestor(b1, b2, allBlocks) \/ IsAncestor(b2, b1, allBlocks)

(* 
Leader/window schedule — alignment with Alpenglow (whitepaper refs in parentheses)

• Leader(slot) == WindowLeader[WindowIndex(slot)]:
  Alpenglow assigns a designated leader to every slot and groups consecutive slots
  into a fixed-length “leader window”; the leader schedule is determined by a 
  (threshold) VRF. Mapping a slot to its window index (WindowIndex) and then to 
  that window’s leader (WindowLeader) is a faithful implementation of this model. (p. 2)

• ASSUME ∀ k ∈ {WindowIndex(s) : s ∈ Slots} : WindowLeader[k] ∈ Validators
  Leaders are drawn from the validator set (the set of nodes with stake); the 
  schedule selects a validator for each window/slot via the VRF. (p. 2)

• FirstSlotOfWindow(slot):
  The paper reasons about “the first slot of the leader window” (e.g., ParentReady 
  is defined specifically for the first slot; timeouts are set for all i ∈ windowSlots(s)).
  Computing the window’s start from a fixed window length is a standard implementation 
  detail consistent with these references. (pp. 21 (ParentReady as “first of its leader window”), 
  23 (Definition 17, timeouts over windowSlots(s)), 25 (firstSlot boolean in Algorithm 2))

• IsFirstSlotOfWindow(slot) == (slot = FirstSlotOfWindow(slot)):
  Algorithm 2 explicitly branches on whether s “is the first slot in leader window,” 
  matching this predicate. (p. 25)

• LeaderMatchesSchedule(b) == (b.leader = Leader(b.slot)):
  Blocks are produced by the leader for the window (“Block creation for leader window 
  starting with slot s”), and Rotor describes the leader (sender) who broadcasts slices. 
  Checking that the block’s producer/signature matches the scheduled leader for slot s 
  reflects the protocol’s assumption that the leader authors the block. (pp. 27 (Alg. 3), 15 (Rotor: leader/sender))
*)

WindowIndex(slot) ==
    IF slot = 0 THEN 0 ELSE (slot - 1) \div WindowSize

Leader(slot) == WindowLeader[WindowIndex(slot)]

ASSUME \A k \in {WindowIndex(s) : s \in Slots} : WindowLeader[k] \in Validators

FirstSlotOfWindow(slot) ==
    IF slot = 0 THEN 0
    ELSE ((slot - 1) \div WindowSize) * WindowSize + 1

IsFirstSlotOfWindow(slot) ==
    slot = FirstSlotOfWindow(slot)

LeaderMatchesSchedule(b) == b.leader = Leader(b.slot)

(* 
WindowSlots(slot) and Tip(chain) — Whitepaper grounding

• Leader windows and windowSlots:
  – Algorithm 2 defines: “function windowSlots(s): return array with slot numbers
    of the leader window with slot s.” (p. 25)
  – Each slot has a designated leader; each leader controls a fixed number of
    consecutive slots (the leader window). (p. 10)
  – When ParentReady(s, …) is emitted for the first slot s of a window, timeouts
    are scheduled for all i ∈ windowSlots(s). (Definition 17, p. 23)
  – The leader of the window beginning with slot s produces blocks for all
    slots windowSlots(s). (p. 26)

• First slot of window and indexing:
  – The paper distinguishes “the first slot in the leader window” and uses it
    to drive downstream logic (e.g., timeouts). (p. 23)
  – Epoch slots are natural numbers s = 1 … L (p. 10); the chain begins at a
    notional genesis block (p. 11). Modeling WindowSlots with s ≥ 1 is consistent
    with this indexing and omits genesis from the slot set.

• Tip(chain) via maximal slot:
  – Blocks are ordered by natural-numbered slots, with child.slot > parent.slot
    (p. 11). On any linear chain, the block with the maximum slot is the latest.
  – The CHOOSE definition “x ∈ chain : ∀ y ∈ chain : x.slot ≥ y.slot” therefore
    selects the tip under the paper’s slot order.

References: p. 10 (slots, leader windows), p. 11 (genesis, strict slot order),
p. 23 (Def. 17 timeouts over windowSlots), p. 25 (Alg. 2: windowSlots),
p. 26 (leader produces all slots in windowSlots).
*)

WindowSlots(slot) ==
    LET first == FirstSlotOfWindow(slot)
    IN {s \in Slots : 
        /\ s >= first 
        /\ s < first + WindowSize
        /\ s >= 1}

\* WindowSlotsSeq returns an ordered sequence for timeout scheduling (Algorithm 2, line 4-5).
\* The paper uses "for i \in windowSlots(s)" with timeout formula (i - s + 1) requiring order.
WindowSlotsSeq(slot) ==
    LET first == FirstSlotOfWindow(slot)
    IN [ i \in 1..WindowSize |-> first + i - 1 ]

Tip(chain) == CHOOSE x \in chain : \A y \in chain : x.slot >= y.slot


(* 
ExtendsChain / AllBlocksValid / UniqueBlocksPerSlot / SingleChain / UniqueBlockHashes
— Alpenglow whitepaper grounding

• Parent linkage and slot monotonicity:
  – Each block's data M includes slot(parent(b)) and hash(parent(b)), enabling
    exact parent–child linkage checks. (p. 15, Definition 3)
  – The protocol orders blocks by natural-numbered slots, with child.slot > parent.slot.
    (p. 11)
  – Selecting the chain tip as the maximal-slot block matches this slot order. (p. 11)
  → ExtendsChain(newBlock, existingChain) requiring ValidParentChild(tip,newBlock)
    and newBlock.slot > tip.slot is consistent with the model.
  – Precondition: ExtendsChain assumes existingChain is already linear (e.g., satisfies
    SingleChain); if multiple blocks share the max slot, CHOOSE picks one arbitrarily.
    This aligns with reasoning about finalized chains (p. 11).

• Validity wrapper:
  – Structural form of a block (p. 15, Def. 3) and block-hash definition (p. 15, Def. 4)
    underpin a well-formedness predicate; AllBlocksValid simply lifts it over a set.

• Finalized uniqueness per slot & linearity:
  – “Finalized blocks form a single chain of parent–child links.” (p. 11)
  – With child.slot > parent.slot (p. 11), a linear chain cannot contain two different
    blocks at the same slot; hence UniqueBlocksPerSlot over finalized blocks.
  – SingleChain over finalized blocks is exactly the whitepaper’s statement; requiring
    pairwise ancestry-comparability captures linearity. (p. 11; p. 15, Definition 5)

• Hash uniqueness modeling:
  – The paper assumes a collision-resistant hash function (e.g., SHA256). (p. 12)
  – Block hash is defined as the Merkle-root over the block’s slices. (p. 15, Definition 4)
  – Modeling UniqueBlockHashes(S) (“equal hash ⇒ equal block”) reflects the standard
    cryptographic assumption consistent with these definitions.

References: p. 11 (Correctness: single finalized chain; child.slot > parent.slot),
p. 12 (collision-resistant hash function), p. 15 (Definition 3: block & parent identifiers;
Definition 4: block hash; Definition 5: ancestor/descendant).
*)

ExtendsChain(newBlock, existingChain) ==
    /\ existingChain # {}
    /\ LET tip == Tip(existingChain) IN
        /\ ValidParentChild(tip, newBlock)
        /\ newBlock.slot > tip.slot

AllBlocksValid(blocks) ==
    \A b \in blocks : IsValidBlock(b)

UniqueBlocksPerSlot(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        b1.slot = b2.slot => b1.hash = b2.hash

SingleChain(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        ComparableByAncestry(b1, b2, finalizedBlocks)

UniqueBlockHashes(S) ==
    \A b1, b2 \in S : (b1.hash = b2.hash) => b1 = b2

=============================================================================
