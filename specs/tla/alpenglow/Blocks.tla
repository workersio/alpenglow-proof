---------------------------- MODULE Blocks ----------------------------
(***************************************************************************
 * BLOCK STRUCTURE AND RELATIONSHIPS FOR ALPENGLOW
 *
 * What this module specifies and where it comes from in the whitepaper:
 *   • §1.1 (:53, :222) — slots, designated leaders, public (VRF-based) schedule.
 *   • §2.1 (Def. 3–5; :351, :357, :363) — block contents, block hash, ancestry.
 *   • §2.7 (and Alg. 3; :678, :759) — fixed-length leader windows and creation.
 *   • Correctness overview (:243) & Theorem 1 (:930) — single-chain finality.
 *
 * This file gives the core “data types” and helper predicates for blocks,
 * ancestry, and leader windows used by the higher-level protocol modules.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Messages

\* ============================================================================
\* CONSTANTS (whitepaper mapping: §1.1, §2.1, §2.7)
\* ============================================================================

CONSTANTS
    GenesisHash,     \* Abstract hash of genesis (Def. 4 notion; :357)
    WindowSize,      \* Fixed consecutive slots per leader window (§2.7; :678)
    WindowLeader     \* Window-indexed leader map (VRF abstraction; §1.1; :222)

ASSUME
    /\ GenesisHash \in BlockHashes
    /\ WindowSize \in Nat \ {0}             \* Window size must be positive (§2.7)
    /\ 0 \in Slots                           \* Genesis uses slot 0 (modeling choice)

\* ============================================================================
\* BLOCK STRUCTURE (whitepaper §2.1, Def. 3–5)
\* ============================================================================

(***************************************************************************
 * What a block records (Def. 3 :351 → abstracted here):
 * - slot   — creation slot (Nat) (:53, :351)
 * - hash   — unique identifier for the block (Def. 4 :357; collision-resistant)
 * - parent — hash of the parent block (lineage pointer; Def. 3/5 :351/:363)
 * - leader — validator that proposed the block (explicit in our model; :53)
 *
 * Rationale:
 * - The data-plane details (slices/shreds) are abstracted away; the control-
 *   plane fields above are sufficient for safety and window reasoning.
 ***************************************************************************)

Block == [
    slot: Slots,
    hash: BlockHashes,
    parent: BlockHashes,
    leader: Validators
]

\* Def. 3–4: a block carries its parent’s identifier and a hash; we add
\* leader explicitly to track proposer identity (cf. §1.1, :53).

\* Genesis modeling (paper uses notional genesis; we model it explicitly):
\* - The paper reasons “from genesis” but does not prescribe a representation.
\* - We encode genesis as slot 0 and self-parented; this simplifies ancestry.
GenesisBlock == [
    slot |-> 0,
    hash |-> GenesisHash,
    parent |-> GenesisHash,  \* Self-parented sentinel for ancestry termination
    leader |-> CHOOSE v \in Validators : TRUE  \* Arbitrary; leader is irrelevant
]

\* Note: “self-parented” is a specification convention, not a paper mandate.
\* It aligns with Def. 5’s lineage and the correctness prose at :243.

\* Auxiliary predicate: characterize the genesis block shape explicitly.
IsGenesis(b) ==
    /\ b.slot = 0
    /\ b.hash = GenesisHash
    /\ b.parent = GenesisHash

\* ============================================================================
\* BLOCK VALIDATION (format/typing per Def. 3–5; paper §2.1)
\* ============================================================================

\* Well-typed block predicate (local format only):
\* - Mirrors Def. 3–4 types; disallows self-parenting for non-genesis (Def. 5).
\* - Parent existence and slot ordering are enforced by ValidParentChild and
\*   by proposer actions (Alg. 3 :759); not here by design.
\* - Schedule adherence is checked with LeaderMatchesSchedule(b) where needed.
IsValidBlock(b) ==
    /\ b.slot \in Slots
    /\ b.hash \in BlockHashes
    /\ b.parent \in BlockHashes
    /\ b.leader \in Validators
    /\ b.slot > 0 => b.parent # b.hash  \* Non-genesis blocks can't self-reference
    /\ (b.slot = 0 => IsGenesis(b))      \* If slot is 0, it must be the (unique) genesis shape

\* Mapping and rationale:
\* - Slots and leader per §1.1 (:53); hash/parent per Def. 3–4 (:351, :357).
\* - Non-genesis cannot self-parent (Def. 5 lineage semantics; :363).
\* - We explicitly constrain slot 0 to the canonical genesis representation.

\* Two different blocks for the same slot (safety lemmas 23–24):
\* - Used to express and rule out slot-level conflicts via certificates.
\* - See §2.4 Lemma 23/24 and Theorem 1 (single chain).

\* Whitepaper refs: slots and leaders (§1.1 :53), hashing (Def. 4 :357),
\* uniqueness in notarization/finalization (Lemma 24 :855, Thm. 1 :930).

\* Parent-child relationship (lineage per Def. 5; creation per §2.7/Alg. 3):
\* - Child references parent hash and has a strictly higher slot.
\* - Alg. 3 builds step-by-step across a window; we keep `parent.slot < child.slot`
\*   to allow harmless slot gaps in abstract reasoning if needed.
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

\* Well-formedness lemma: a notar-vote constructed for a valid block is a
\* valid vote (content-only; signatures are abstracted).
THEOREM CreateNotarVoteForBlockWellTyped ==
    \A v \in Validators, b \in Block :
        IsValidBlock(b) => IsValidVote(CreateNotarVoteForBlock(v, b))

(***************************************************************************
 * Create a notar-fallback vote for a given block. Like the notar wrapper,
 * this preserves the slot–hash pairing and avoids call‑site mismatches.
 * Signatures are abstracted; only logical content matters (see §1.6).
 ***************************************************************************)
CreateNotarFallbackVoteForBlock(v, b) ==
    CreateNotarFallbackVote(v, b.slot, b.hash)

\* Well-formedness lemma: a notar-fallback vote constructed for a valid
\* block is a valid vote (content-only; signatures are abstracted).
THEOREM CreateNotarFallbackVoteForBlockWellTyped ==
    \A v \in Validators, b \in Block :
        IsValidBlock(b) => IsValidVote(CreateNotarFallbackVoteForBlock(v, b))

\* ============================================================================
\* ANCESTRY RELATIONSHIPS (whitepaper §2.1, Def. 5; safety §2.6/Thm. 1)
\* ============================================================================

(***************************************************************************
 * Ancestry (Def. 5 :363) underpins safety:
 * - If A is an ancestor of B, B’s history includes A (parent pointers).
 * - Finalized blocks form a single chain: any two are comparable by ancestry
 *   (overview :243; Theorem 1 :930). The finalized set is kept closed under
 *   ancestors operationally (FinalizeBlock unions GetAncestors).
 ***************************************************************************)

\* Ancestor test (Def. 5): true iff following parent links from b2 reaches b1.
\* Universe parameter `allBlocks` must contain the ancestry of b2 for completeness.
IsAncestor(b1, b2, allBlocks) ==
    LET
        \* Recursively follow parent links
        RECURSIVE ReachableFrom(_)
        ReachableFrom(b) ==
            IF b = b1 THEN TRUE  \* Found the ancestor!
            ELSE IF b.hash = GenesisHash THEN FALSE  \* Hit genesis (explicit sentinel)
            ELSE 
                \* Find the parent block and continue
                LET parentBlocks == {p \in allBlocks : p.hash = b.parent}
                IN IF parentBlocks = {} THEN FALSE
                   ELSE LET parent == CHOOSE p \in parentBlocks : TRUE
                        IN ReachableFrom(parent)
    IN b1 = b2 \/ ReachableFrom(b2)  \* A block is its own ancestor

\* Descendant is the inverse of ancestor (Def. 5 :363).
IsDescendant(b1, b2, allBlocks) == 
    IsAncestor(b2, b1, allBlocks)

\* All ancestors of b (includes b itself per Def. 5).
\* Used during finalization to ensure ancestor-closure of finalized sets (:541).
GetAncestors(b, allBlocks) ==
    {ancestor \in allBlocks : IsAncestor(ancestor, b, allBlocks)}

\* Comparable by ancestry iff one is an ancestor of the other.
ComparableByAncestry(b1, b2, allBlocks) ==
    IsAncestor(b1, b2, allBlocks) \/ IsAncestor(b2, b1, allBlocks)

\* Same-chain iff comparable by ancestry. When used over finalized sets, this
\* encodes Theorem 1 (single-chain finality) provided finalization keeps
\* ancestor-closure (as in MainProtocol).
InSameChain(b1, b2, allBlocks) ==
    ComparableByAncestry(b1, b2, allBlocks)

\* ============================================================================
\* LEADER WINDOWS (whitepaper §1.1, §2.7; Alg. 3)
\* ============================================================================

(***************************************************************************
 * Leaders control fixed-length consecutive slots (a “window”) (§1.1 :53, §2.7 :678).
 * Example with WindowSize = 4: 1–4, 5–8, 9–12, … share the same leader.
 * First-slot semantics are special for timeouts/ParentReady (Def. 17 :613).
 ***************************************************************************)

\* Window index (groups slots into windows). Helps state/derive window facts.
\* Whitepaper: public schedule and windows (§1.1 :222, §2.7 :678).
WindowIndex(slot) ==
    IF slot = 0 THEN 0 ELSE (slot - 1) \div WindowSize

\* Leader abstraction: VRF-chosen per leader window. We model it with a
\* window-indexed function, which immediately implies window consistency.
Leader(slot) == WindowLeader[WindowIndex(slot)]

\* Type assumption for the schedule abstraction we actually index into.
ASSUME \A k \in {WindowIndex(s) : s \in Slots} : WindowLeader[k] \in Validators

\* First slot of the window containing `slot` (ParentReady gating :613).
FirstSlotOfWindow(slot) ==
    IF slot = 0 THEN 0
    ELSE ((slot - 1) \div WindowSize) * WindowSize + 1

\* Check if this slot is the first in its window
IsFirstSlotOfWindow(slot) ==
    slot = FirstSlotOfWindow(slot)

\* Leader-schedule adherence helper for blocks.
LeaderMatchesSchedule(b) == b.leader = Leader(b.slot)

\* Leaders stay fixed across a window (§2.7 :678; Alg. 3 :759). This is a
\* theorem here because `Leader` is defined via `WindowLeader[WindowIndex(_)]`.
LeaderScheduleWindowConsistency ==
    \A s \in Slots : Leader(s) = Leader(FirstSlotOfWindow(s))

THEOREM LeaderScheduleWindowConsistency

\* Interpretation: Alg. 3 lets a leader produce several consecutive slots.
\* These helpers compute window starts and capture “same leader across window”.

\* All slots in the same window as `slot` (WINDOWSLOTS in paper :678).
\* Note: Genesis (slot 0) is not a production slot; callers typically restrict
\* to production domains when scheduling timeouts per Def. 17 (:613).
WindowSlots(slot) ==
    LET first == FirstSlotOfWindow(slot)
    IN {s \in Slots : 
        /\ s >= first 
        /\ s < first + WindowSize
        /\ s >= 1}

\* Returns the set of slot numbers owned by the leader of `slot`.

\* Domain sanity: FirstSlotOfWindow(s) ∈ Slots when Slots is prefix-closed.
THEOREM FirstSlotOfWindowInSlots ==
    \A s \in Slots : FirstSlotOfWindow(s) \in Slots

\* ============================================================================
\* CHAIN OPERATIONS (using Def. 5 ancestry; §2.7 creation discipline)
\* ============================================================================

\* Note: A "chain" is represented as a set of blocks, not a sequence.
\* Ordering-sensitive operations rely on the slot field or ancestry relations.

\* Query whether a chain has a block at a specific slot

\* Select the (unique) block at a specific slot in a chain.

\* Complete chain (ancestors) from genesis to b (Def. 5 :363).

\* Select the tip (maximum-slot element) of a non-empty chain
Tip(chain) == CHOOSE x \in chain : \A y \in chain : x.slot >= y.slot

\* Proper extension: the new block references the tip and increases slot.
\* Alg. 3 extends slot-by-slot; we keep `>` (vs `= +1`) at this abstraction.
ExtendsChain(newBlock, existingChain) ==
    /\ existingChain # {}
    /\ LET tip == Tip(existingChain) IN
        /\ ValidParentChild(tip, newBlock)
        /\ newBlock.slot > tip.slot

\* ============================================================================
\* INVARIANTS FOR VERIFICATION (safety & typing alignment)
\* ============================================================================

\* All blocks are well-typed (Def. 3–4 fields; Def. 5 non-self-parent).
AllBlocksValid(blocks) ==
    \A b \in blocks : IsValidBlock(b)

\* No two different finalized blocks share a slot (safety corollary).
\* Implied by single-chain safety; useful as a focused check.
UniqueBlocksPerSlot(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        b1.slot = b2.slot => b1.hash = b2.hash

\* Finalized blocks form a single chain (Theorem 1 :930; overview :243).
\* Requires finalized sets to be closed under ancestry (operationally enforced).
SingleChain(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        InSameChain(b1, b2, finalizedBlocks)

\* Hashes are unique within any set of blocks (guards CHOOSE determinism).
\* Paper assumes collision resistance (Def. 4 :357); this predicate documents
\* the uniqueness expectation where it matters locally in the model.
UniqueBlockHashes(S) ==
    \A b1, b2 \in S : (b1.hash = b2.hash) => b1 = b2

=============================================================================
