---------------------------- MODULE Blocks ----------------------------
(***************************************************************************
 * BLOCK STRUCTURE AND RELATIONSHIPS FOR ALPENGLOW
 *
 * Whitepaper grounding (Alpenglow v1.1):
 *   • Slots, leaders, fixed-length leader windows, public VRF schedule:
 *       §1.1 overview—leader(s), leader window, threshold VRF (pp. 9–10)
 *
 *   • Data model: shreds → slices → block; block hash; ancestry:
 *       §2.1, Definitions 1–5 (pp. 14–16): Def. 3 (block & parent identifiers),
 *       Def. 4 (block hash as Merkle root), Def. 5 (ancestor/descendant, reflexive)
 *
 *   • Correctness + linearity of finalized chain and slot order:
 *       §1.5 “Correctness” (p. 11) and Theorem 1 (Safety) (§2.9, pp. 32–33)
 *
 * This module defines the control-plane datatypes and predicates for blocks,
 * ancestry, and leader windows used by higher-level protocol specs.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Messages, Sequences

\* ============================================================================
\* CONSTANTS (whitepaper mapping: §1.1, §2.1, §2.7)
\* ============================================================================

CONSTANTS
    GenesisHash,     \* Abstract hash of genesis (Def. 4; §2.1)
    WindowSize,      \* Fixed consecutive slots per leader window (§1.1)
    WindowLeader     \* Window-indexed leader map (VRF abstraction; §1.1)

ASSUME
    /\ GenesisHash \in BlockHashes
    /\ WindowSize \in Nat \ {0}

(* ------------------------------------------------------------------------------
 * Block Definition — Control-plane abstraction (paper §2.1)
 * ------------------------------------------------------------------------------
 * The paper builds the data-plane hierarchy (shreds→slices) and defines a block b
 * as “the sequence of all slices of a slot … for voting and reaching consensus”.
 * Block data M carries slot(parent(b)) and hash(parent(b)) to link ancestry.  (Def. 3)
 * The block hash hash(b) is a Merkle-root over slice roots r₁..rₖ.            (Def. 4)
 * References: §2.1 Def. 3–4 (pp. 15–16)
 *
 * For protocol reasoning we keep only control-plane metadata:
 *   slot(b), hash(b), parent(b), leader(b).
 * The leader is derivable from the public schedule leader(s) (VRF-set before epoch),
 * but we keep it explicitly for convenience in predicates like LeaderMatchesSchedule.
 * References: §1.1 leader(s)/VRF (pp. 9–10)
 * ------------------------------------------------------------------------------ *)

Block == [
    slot: {0} \cup Slots,
    hash: BlockHashes,
    parent: BlockHashes,
    leader: Validators
]

(* ------------------------------------------------------------------------------
 * Genesis — sentinel root of ancestry (paper §1.5)
 * ------------------------------------------------------------------------------
 * Correctness states: “Every block is associated with a parent (starting at some
 * notional genesis block). Finalized blocks form a single chain of parent-child links.”
 * We model a notional genesis at slot 0 with parent = hash = GenesisHash as a clean
 * termination point for ancestry walks. The epoch iterates through slots s = 1..L.
 * References: §1.5 Correctness (p. 11); §1.1 slot indexing (pp. 9–10)
 * ------------------------------------------------------------------------------ *)

GenesisBlock == [
    slot |-> 0,
    hash |-> GenesisHash,
    parent |-> GenesisHash,  \* Self-parented sentinel (modeling choice consistent with “notional genesis”)
    leader |-> CHOOSE v \in Validators : TRUE  \* Arbitrary; leader irrelevant for genesis
]

IsGenesis(b) ==
    /\ b.slot = 0
    /\ b.hash = GenesisHash
    /\ b.parent = GenesisHash

(* ------------------------------------------------------------------------------
 * IsValidBlock — structural well-formedness for non-genesis blocks
 * ------------------------------------------------------------------------------
 * Non-genesis blocks must have: slot ∈ Slots (protocol slots s ≥ 1), hash/parent in
 * BlockHashes, leader ∈ Validators, and parent ≠ hash. Parent/slot semantics and
 * identifiers come from §2.1 Defs. 3–5; the strict temporal relation (child.slot > parent.slot)
 * is specified by the protocol’s slot order and is checked elsewhere. 
 * References: §2.1 Defs. 3–5 (pp. 15–16); §1.5 slot order (p. 11)
 * ------------------------------------------------------------------------------ *)

IsValidBlock(b) ==
    /\ b.slot \in Slots
    /\ b.hash \in BlockHashes
    /\ b.parent \in BlockHashes
    /\ b.leader \in Validators
    /\ b.parent # b.hash  \* Non-self-parented (excludes genesis)

(* ------------------------------------------------------------------------------
 * ValidParentChild — parent linkage and slot monotonicity
 * ------------------------------------------------------------------------------
 * Child carries slot(parent(b)) and hash(parent(b)) in its data, so we can check
 * child.parent = parent.hash (Def. 3). The protocol mandates child.slot > parent.slot.
 * References: §2.1 Def. 3 (p. 15); §1.5 (p. 11)
 * ------------------------------------------------------------------------------ *)

ValidParentChild(parent, child) ==
    /\ parent.hash = child.parent   \* Child references parent correctly
    /\ parent.slot < child.slot     \* Parent comes before child

(***************************************************************************
 * Vote constructors for a block — typed wrappers
 *
 * Table 5 defines voting messages including NotarVote(slot(b), hash(b)) and
 * NotarFallbackVote(slot(b), hash(b)). These wrappers keep the slot–hash pairing
 * consistent at call sites.
 * Reference: §2.4 Table 5 (p. 20)
 ***************************************************************************)
CreateNotarVoteForBlock(v, b) ==
    CreateNotarVote(v, b.slot, b.hash)

CreateNotarFallbackVoteForBlock(v, b) ==
    CreateNotarFallbackVote(v, b.slot, b.hash)

(* ------------------------------------------------------------------------------
 * Ancestor reasoning (IsAncestor, GetAncestors, ComparableByAncestry)
 * ------------------------------------------------------------------------------
 * Ancestor/descendant is reachability via parent links; the relation is reflexive:
 * “b is its own ancestor and descendant.” (Def. 5)
 * The backward step is enabled by block data containing slot(parent(b)) and hash(parent(b)).
 * (Def. 3)
 * Termination uses the notional genesis block. (§1.5)
 *
 * CHOOSE on parents assumes hash uniqueness. The paper assumes collision-resistant
 * hashing and shows encode/decode properties that make the Merkle root r uniquely
 * associated with payload M, with a pass/fail decode check. (§1.6)
 *
 * ------------------------------------------------------------------------------ *)

IsAncestor(b1, b2, allBlocks) ==
    LET
        RECURSIVE ReachableFrom(_)
        ReachableFrom(b) ==
            IF b = b1 THEN TRUE  \* Found the ancestor!
            ELSE IF b.hash = GenesisHash THEN (b1.hash = GenesisHash)  \* Hit genesis; check if b1 is genesis
            ELSE 
                \* Find the parent block and continue
                LET parentBlocks == {p \in allBlocks : p.hash = b.parent}
                IN IF parentBlocks = {} THEN FALSE
                   ELSE LET parent == CHOOSE p \in parentBlocks : TRUE
                        IN ReachableFrom(parent)
    IN b1 = b2 \/ ReachableFrom(b2)  \* A block is its own ancestor

GetAncestors(b, allBlocks) ==
    {ancestor \in allBlocks : IsAncestor(ancestor, b, allBlocks)}

(* ------------------------------------------------------------------------------
 * AncestorAtSlot - Find the specific ancestor at a given slot
 * ------------------------------------------------------------------------------
 * For Lemma 30 (ancestor coverage, §2.9): given a block b and a slot s, return
 * the unique ancestor of b that occupies slot s, or NoBlock if none exists.
 *
 * Whitepaper reference: Lemma 30 requires checking that "for every slot s' in
 * the window, the corresponding ancestor has ≥40% notar votes or a notar-
 * fallback certificate." This helper enables that per-slot ancestor lookup.
 *
 * Precondition: allBlocks forms a valid chain (no forks in b's ancestry).
 * Returns: The ancestor block a where a.slot = targetSlot, or NoBlock.
 * ------------------------------------------------------------------------------ *)

AncestorAtSlot(b, targetSlot, allBlocks) ==
    LET ancestors == GetAncestors(b, allBlocks)
        matching == {a \in ancestors : a.slot = targetSlot}
    IN IF matching = {} 
       THEN NoBlock
       ELSE CHOOSE a \in matching : TRUE

ComparableByAncestry(b1, b2, allBlocks) ==
    IsAncestor(b1, b2, allBlocks) \/ IsAncestor(b2, b1, allBlocks)

(* ------------------------------------------------------------------------------
 * Leader/window schedule (Leader, WindowIndex, FirstSlotOfWindow, IsFirstSlot)
 * ------------------------------------------------------------------------------
 * Each slot has a designated leader; leaders control fixed-length “leader windows”,
 * and a threshold VRF yields a publicly known leader schedule. (§1.1)
 * The protocol reasons about windowSlots(s) and branches on “first slot in leader
 * window”; ParentReady is only for the first slot. (Alg. 2; Def. 15; Def. 17)
 *
 * We model this with a fixed WindowSize and a mapping WindowLeader[WindowIndex(s)].
 * ------------------------------------------------------------------------------ *)

WindowIndex(slot) ==
    IF slot = 0 THEN 0 ELSE (slot - 1) \div WindowSize

Leader(slot) == WindowLeader[WindowIndex(slot)]

(* Domain/range sanity for the schedule: leader(s) maps to a node; schedule known
 * before epoch; leaders are drawn from the node set for the epoch. (§1.1)
 * *)
ASSUME
    /\ {WindowIndex(s) : s \in Slots} \subseteq DOMAIN WindowLeader
    /\ \A k \in {WindowIndex(s) : s \in Slots} : WindowLeader[k] \in Validators

FirstSlotOfWindow(slot) ==
    IF slot = 0 THEN 0
    ELSE ((slot - 1) \div WindowSize) * WindowSize + 1

IsFirstSlotOfWindow(slot) ==
    slot = FirstSlotOfWindow(slot)

LeaderMatchesSchedule(b) == b.leader = Leader(b.slot)

(* ------------------------------------------------------------------------------
 * WindowSlots / WindowSlotsSeq and Tip(chain)
 * ------------------------------------------------------------------------------
 * windowSlots(s) (Alg. 2) returns the slot numbers of the leader window for s and
 * is used to set timeouts across the window from the first slot (Def. 17).

 * The leader of the window beginning with slot s produces blocks for all slots
 * in windowSlots(s). (§2.7 Block Creation)
 * On any linear chain ordered by slots with child.slot > parent.slot, the max-slot
 * element is the tip. (§1.5)
 * ------------------------------------------------------------------------------ *)

WindowSlots(slot) ==
    LET first == FirstSlotOfWindow(slot)
    IN {s \in Slots : 
        /\ s >= first 
        /\ s < first + WindowSize
        /\ s >= 1}

\* Sequence form for ordered iteration in timeouts (Alg. 2 “array with slot numbers”).
WindowSlotsSeq(slot) ==
    LET first == FirstSlotOfWindow(slot)
    IN [ i \in 1..WindowSize |-> first + i - 1 ]

Tip(chain) == CHOOSE x \in chain : \A y \in chain : x.slot >= y.slot

(* ------------------------------------------------------------------------------
 * Chain linearity and uniqueness helpers
 * ------------------------------------------------------------------------------
 * Finalized blocks form a single chain of parent-child links, and when a block is
 * finalized, all ancestors are finalized as well. (§1.5 correctness; also noted in §2.6)
 * At most one block can be notarized in a slot (Lemma 24), and “fast/slow” rules
 * ensure consistent uniqueness across finalization. (§2.9 Lemmas 23–25)
 * UniqueBlockHashes models the crypto assumptions: collision-resistant hash and
 * encode/decode guarantee that the Merkle root r is uniquely associated with M.
 * (§1.6)
 * ------------------------------------------------------------------------------ *)

ExtendsChain(newBlock, existingChain) ==
    /\ existingChain # {}
    /\ LET tip == Tip(existingChain) IN
        /\ ValidParentChild(tip, newBlock)
        /\ newBlock.slot > tip.slot

AllBlocksValid(blocks) ==
    \A b \in blocks : IsGenesis(b) \/ IsValidBlock(b)

\* If same slot, must have same hash
UniqueBlocksPerSlot(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        b1.slot = b2.slot => b1.hash = b2.hash


SameChain(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        ComparableByAncestry(b1, b2, finalizedBlocks)

UniqueBlockHashes(S) ==
    \A b1, b2 \in S : (b1.hash = b2.hash) => b1 = b2

=============================================================================
