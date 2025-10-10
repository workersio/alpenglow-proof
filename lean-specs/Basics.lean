/-
  Alpenglow Proof Basics

  This module collects the core data structures shared across the Lean
  formalization of the Alpenglow protocol.  In particular we capture
  the whitepaper definitions for shreds, slices, and blocks so that the
  subsequent lemmas can refer to a single source of truth.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

namespace Alpenglow

universe u v w x

/-- Slots, slice indices, and shred indices are natural numbers in the formalization,
    matching the whitepaper's notation. -/
abbrev Slot := Nat            -- [p.14, Defs. 1–2 use s,t]
abbrev SliceIndex := Nat      -- [p.14, Defs. 1–2]
abbrev ShredIndex := Nat      -- [p.14, Def. 1 (i)]

/-- A helper object bundling shred payload and its Merkle path `(d_i, π_i)`. -/
structure MerkleWitness (Data : Type u) (Path : Type v) where
  d : Data
  pi : Path
  deriving Repr
-- [p.16 “Merkle path”; p.12 padding notion; p.15 full tree]

/-! ### Merkle hashing infrastructure -/

namespace Merkle

/-- Abstract interface describing the hashing functions used when constructing
    Merkle trees for block data.  The `padding` value supplies the hash inserted
    when completing the tree to the next power-of-two number of leaves, matching
    the whitepaper's requirement that the tree be full. -/
structure Hasher (Hash : Type u) where
  leafLabel : Hash → Hash
  branch : Hash → Hash → Hash
  padding : Hash
-- [p.12 padding to next power of two; p.15 full binary tree]

variable {Hash : Type u} (H : Hasher Hash)

/-! We follow the whitepaper's Merkle definition precisely:
    - Apply the leaf-domain label only to base leaves (including padding ⊥),
    - Internal nodes are computed by `branch` only (no leaf label),
    - The tree is completed to the next power-of-two number of leaves by
      padding with ⊥ at the leaf level (p.15, Def. 4).
 -/

/-- Smallest power-of-two `m` with `m ≥ n`. For `n = 0`, returns `1`. -/
def nextPow2AtLeast : Nat → Nat
  | 0 => 1
  | n + 1 =>
      let m := nextPow2AtLeast n
      if (n + 1) ≤ m then m else m * 2

/-- Label the given leaves and pad with `⊥` (via `padding`) so that the
    resulting list has length a power of two, as required by the whitepaper. -/
def padLeavesToPow2 (xs : List Hash) : List Hash :=
  let k := xs.length
  let m := nextPow2AtLeast k
  let base := xs.map H.leafLabel
  let padLeaf := H.leafLabel H.padding
  base ++ List.replicate (m - k) padLeaf

/-- Combine one internal level by branching adjacent nodes. Assumes inputs are
    already leaf-labeled if they are leaves. Internal nodes are not leaf-labeled. -/
def level (xs : List Hash) : List Hash :=
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: rest => H.branch x y :: level rest
-- [p.12–15: internal nodes are hashes of children; no duplication beyond leaf padding]

/-- Recursively compute a Merkle root with an explicit fuel argument to ensure
    structural termination in Lean. The fuel is typically the length of the
    input list. -/
def rootAux : Nat → List Hash → Hash
  | _, [] => H.leafLabel H.padding
  | _, [x] => x
  | 0, _ :: _ :: _ => H.leafLabel H.padding
  | Nat.succ fuel, xs@(_ :: _ :: _) =>
      rootAux fuel (level H xs)
-- [p.12 padding default; structural recursion for totality (formalization detail)]

/-- Compute the Merkle root for an arbitrary list of leaf hashes.
    The algorithm follows the whitepaper description:
    - Pad the leaves to the next power-of-two with `⊥`,
    - Apply `leafLabel` to all base leaves (including `⊥`),
    - Combine internal nodes using `branch` only (no leaf labels). -/
def root (xs : List Hash) : Hash :=
  let leaves := padLeavesToPow2 H xs
  rootAux H leaves.length leaves
-- [p.15 Def. 4: block hash as Merkle root over slice roots]
end Merkle

/-- Definition 1 (shred) from the whitepaper. -/
structure Shred (Data : Type u) (Path : Type v) (Hash : Type w)
    (Signature : Type x) where
  s : Slot
  t : SliceIndex
  i : ShredIndex
  z : Bool
  r : Hash
  witness : MerkleWitness Data Path
  sigma : Signature
  deriving Repr
-- [p.14, Def. 1: fields s,t,i, z flag, Merkle witness, signature]

/-- Definition 2 (slice) from the whitepaper. -/
structure Slice (Message : Type u) (Hash : Type v) (Signature : Type w) where
  s : Slot
  t : SliceIndex
  z : Bool
  r : Hash
  M : Message
  sigma : Signature
  deriving Repr
-- [p.14, Def. 2: (s, t, z_t, r_t, M, σ)]

namespace Slice

variable {Message : Type u} {Hash : Type v} {Signature : Type w}

/-- Convenience: the metadata tuple `(s, t, z_t, r_t)` of a slice. -/
def header (sl : Slice Message Hash Signature) :
    Slot × SliceIndex × Bool × Hash :=
  (sl.s, sl.t, sl.z, sl.r)
-- [p.14, Def. 2 metadata projection]
end Slice

/-! We write `k = b.sliceCount` to mirror the notation in Definition 3. -/
/-- Definition 3 (block) from the whitepaper.  A block is a sequence of slices
    that all belong to the same slot. -/
structure Block (Message : Type u) (Hash : Type v) (Signature : Type w) where
  s : Slot
  slices : List (Slice Message Hash Signature)
  deriving Repr
-- [p.15, Def. 3: same-slot sequence of slices]

namespace Block

variable {Message : Type u} {Hash : Type v} {Signature : Type w}

/-- Number of slices stored in the block. -/
@[simp]
def sliceCount (b : Block Message Hash Signature) : Nat :=
  b.slices.length
-- [p.15, Def. 3 notation k = |slices|]

/-- Optional access to the last slice of the block. -/
def lastSlice?
    (b : Block Message Hash Signature) :
    Option (Slice Message Hash Signature) :=
  b.slices.getLast?
-- [p.14–15: uses terminal flag on last slice]

/-- Extract the decoded slice data for the block. -/
def data (b : Block Message Hash Signature) : List Message :=
  b.slices.map (·.M)
-- [p.14–15: block carries messages from slices]

/-- Extract the Merkle roots from each slice. -/
def sliceRoots (b : Block Message Hash Signature) : List Hash :=
  b.slices.map (·.r)
-- [p.15, Def. 4 input leaves r_t]

/-- Definition 4 (block hash).  The block hash is the root of the complete
    Merkle tree obtained from the slice roots `r_t`. -/
def hash (b : Block Message Hash Signature) (H : Merkle.Hasher Hash) : Hash :=
  Merkle.root H (b.sliceRoots)
-- [p.15, Def. 4; also referenced p.40]

/-- Checks that the block contains a designated terminal slice. -/
def hasTerminalSlice (b : Block Message Hash Signature) : Prop :=
  match b.lastSlice? with
  | some sl => sl.z = true
  | none => False
-- [p.14–15: terminal flag z_t = 1 on final slice]

/-- Predicate stating that every slice in the block belongs to the same slot. -/
def allSlicesInSlot (b : Block Message Hash Signature) : Prop :=
  ∀ {sl}, sl ∈ b.slices → sl.s = b.s
-- [p.15, Def. 3: same-slot condition]

/-- Helper predicate capturing the typical well-formedness conditions mentioned
    in the whitepaper: slices belong to the same slot and the terminal slice is
    marked with `z_t = 1`.  Further constraints (e.g. bounds on size) can be
    layered on top as needed by the proofs. -/
def valid (b : Block Message Hash Signature) : Prop :=
  (b.slices ≠ []) ∧
    b.allSlicesInSlot ∧
    b.hasTerminalSlice ∧
    ∀ {sl}, sl ∈ b.slices.dropLast → sl.z = false
-- [p.14–15: z_t usage; Def. 3 requires same slot; terminal marker discipline]
end Block

/-
  ============================
  Additions for Theorem 1 setup
  ============================
-/

-- Node ids / crypto / headers / ancestry / stake / votes / certs / pool / events / schedule
-- Page references follow the whitepaper sections indicated in the cross-walk.

abbrev NodeId := Nat
-- [p.8 validators; nodes throughout pp.1–11]

variable {Message : Type u} {Hash : Type v} {Signature : Type w}

/-- Signature verification relation (opaque; implemented by the crypto layer). -/
class SigScheme (Signature : Type*) (Hash : Type*) (NodeId : Type*) where
  verify : NodeId → Hash → Signature → Prop
-- [pp.12, 14, 16, 19–20: signatures/verification mentions]

/-- Canonical identifier for a block (hash of the block in the paper). -/
abbrev BlockId (Hash : Type _) := Hash
-- [p.15 Def. 4; also p.42–43 when talking about ancestors by id]

/-- A minimal header that captures exactly what Theorem 1 needs:
    slot number, parent pointer, and the block's own id. -/
structure Header (Hash : Type _) where
  s        : Slot
  parentId : Option Hash  -- none for genesis
  id       : Hash
  deriving DecidableEq
-- [p.15: parent relations implied; pp.31–33, 42–43: parent/ancestor usage]

/-- A "node" in the block tree: header + the body you already defined. -/
structure BlockNode
    (Message : Type u) (Hash : Type v) (Signature : Type w) where
  header : Header Hash
  body   : Block Message Hash Signature
-- [p.15 Def. 3 (body) + pp.31–33 parent/slot interplay]

namespace BlockNode

/-- Immediate-parent relation on headers. -/
def isParentOf (p c : Header Hash) : Prop :=
  c.parentId = some p.id ∧ p.s < c.s
-- [pp.31–33: parent older slot; pointer equality via ids]

/-- Ancestor/descendant (reflexive–transitive closure of `isParentOf`). -/
inductive IsAncestor (root : Header Hash) : Header Hash → Prop
| refl  : IsAncestor root root
| step  : ∀ {mid child}, IsAncestor root mid → isParentOf mid child → IsAncestor root child
-- [pp.11, 15, 31–33, 42–43: ancestry language]

def IsDescendant (child root : Header Hash) : Prop := IsAncestor root child
-- [pp.31–33, 42–43]
end BlockNode

/-- Nonnegative stake weights. The actual sum-to-1 constraint and big operators
    are defined in modules that import Real numbers. -/
structure StakeProfile where
  N           : Nat
  weight      : NodeId → Nat  -- Simplified to Nat for basic module
-- [pp.4–5 overview of stake; thresholds p.20–22; used throughout safety proofs]

/-- "Correct" node predicate (Byzantine = ¬correct). Parameter for the protocol. -/
def Correct := NodeId → Prop
-- [pp.4–5, 28–31: correct vs Byzantine]

/-- Byzantine stake bound (paper uses < 20%). Exact constraint deferred to theorem modules. -/
structure AdversaryBound (SP : StakeProfile) (correct : Correct) where
  byzStakeBounded : Prop  -- Actual constraint: byzantine stake < 20%
-- [pp.4–5 overview; pp.28–31 technical lemmas with 20% bound; pp.38–41 recaps]

/-- Vote types used for certificates. -/
inductive VoteType
| notar          -- notarization vote (round 1)
| notarFallback  -- notar-fallback
| skip           -- skip vote for a slot
| skipFallback   -- skip-fallback vote for a slot
| final          -- slow finalization (slot-scoped)
deriving DecidableEq, Repr
-- [p.19 Def. 11 baseline; p.20–22, 28–36, 38, 43–46 for the specific kinds]

/-- Votes are keyed either by slot or by (slot, block). -/
inductive VoteKey (Hash : Type _)
| slot  : Slot → VoteKey Hash
| block : Slot → BlockId Hash → VoteKey Hash
deriving DecidableEq, Repr
-- [pp.19–21 Def. 11; keys attest to slots or (slot,block)]

/-- A vote message from a node with stake. -/
structure Vote (Hash : Type _) (Signature : Type _) where
  voter : NodeId
  kind  : VoteType
  key   : VoteKey Hash
  sig   : Signature
-- [pp.19–21 Def. 11; signatures p.19–20]

/-- A certificate is a set of votes with total stake weight ≥ threshold. -/
structure Certificate (Hash : Type _) where
  kind        : VoteType
  key         : VoteKey Hash
  voters      : Finset NodeId
  weightSum   : Nat  -- Simplified to Nat for basic module
  thrOK       : Prop   -- "weightSum ≥ τ(kind)" (to be specialized)
-- [pp.20–21 Def. 12; thresholds also p.22, p.10 overview]

/-- Named certificates for clarity. -/
def NotarCert   (Hash : Type _) := Certificate Hash  -- [p.19–22, 28–36]
def SkipCert    (Hash : Type _) := Certificate Hash  -- [p.19, 21–22, 28, 30, 32–36]
def FinalCert   (Hash : Type _) := Certificate Hash  -- [p.19, 21, 38, 43–46]
-- Fast-finalization is represented at the theorem level via a higher threshold
-- notarization certificate (block-scoped) rather than a separate kind here.

/-- The local storage of observed votes & certificates. -/
structure Pool (Hash : Type v) : Type (max 1 v) where
  votes        : VoteType → VoteKey Hash → Finset NodeId
  certs        : VoteType → VoteKey Hash → Option (Certificate Hash)
-- [pp.20–23, 27, 29, 32–34: pools of votes/certs; also "pool" p.3, p.49]

namespace Pool
variable {Hash : Type v}

/-- Accessor: notarization certificate for (s,b). -/
def notarCert? (P : Pool Hash) (s : Slot) (b : BlockId Hash) :
    Option (NotarCert Hash) :=
  P.certs VoteType.notar (VoteKey.block s b)
-- [pp.19–22, 28–36]

/-- Accessor: skip certificate for slot s. -/
def skipCert? (P : Pool Hash) (s : Slot) : Option (SkipCert Hash) :=
  P.certs VoteType.skip (VoteKey.slot s)
-- [pp.19, 21–22, 28, 30, 32–36]

/-- Accessor: finalization certificate for slot s. -/
def finalCert? (P : Pool Hash) (s : Slot) :
    Option (FinalCert Hash) :=
  P.certs VoteType.final (VoteKey.slot s)
-- [pp.19, 21, 38, 43–46]

-- No separate accessor for fast-finalization; use notarCert? with a stronger threshold.
end Pool

/-- Events that drive the protocol handlers (Alg. 1/2). -/
inductive Event (Hash : Type _)
| BlockNotarized  (s : Slot) (b : BlockId Hash)
| ParentReady     (s : Slot) (parent : BlockId Hash)
| SafeToNotar     (s : Slot) (b : BlockId Hash)
| SafeToSkip      (s : Slot)
deriving Repr, DecidableEq
-- [Defs. 15–16 p.21; occurrences: ParentReady p.21,23–27,32–37,42;
--  BlockNotarized p.21,23–25,30,33; SafeToNotar p.19,21,24,29–31,34–39;
--  SafeToSkip p.21–22,24,29,34,36–39]

/-- Leader schedule for slots. -/
abbrev LeaderSchedule := Slot → NodeId
-- [“leader” and slots throughout; used with WINDOWSLOTS: p.31,33–37]

/-- The “leader window” for slot s (WINDOWSLOTS(s)). -/
structure LeaderWindow where
  slots : List Slot
  nonempty : slots ≠ []
  deriving Repr
-- [WINDOWSLOTS references p.31, 33–37 (also 23,25,34–36)]

/-- A schedule provides both leader and per-slot windows. -/
structure Schedule where
  leader    : LeaderSchedule
  window    : Slot → LeaderWindow
-- [p.31, 33–37]

/-- A block is notarized if Pool has a notar certificate for (s, b). -/
def Notarized (P : Pool Hash) (h : Header Hash) : Prop :=
  ∃ C, P.notarCert? h.s h.id = some C
-- [pp.19–22, 28–36]

/-- Finalization predicate approximating Def. 14 p.21 without a separate fast-final kind:
    - fast: existence of a block-scoped notar certificate for (s, id) (80% threshold
      is enforced in theorem modules via `FastFinalizationCertValid`).
    - slow: a slot-scoped finalization certificate exists for the slot and the
      block is the notarized block of that slot. -/
inductive Finalized (P : Pool Hash) (h : Header Hash) : Prop
| fast  : (∃ C, P.notarCert? h.s h.id = some C) →
          Finalized P h
| slow  : (∃ C, P.finalCert? h.s = some C) →
          (∃ Cn, P.notarCert? h.s h.id = some Cn) →
          Finalized P h
-- [Def. 14 p.21; fast path uses notar cert with stronger threshold handled elsewhere]

/-- A convenient slot order predicate. -/
def SlotLe (a b : Header Hash) : Prop := a.s ≤ b.s
-- [ordering on slots used throughout; see p.11, 15, 31–33]

/-- Body validity + header-slot coherence. -/
def WellFormed (bn : BlockNode Message Hash Signature) : Prop :=
  bn.body.valid ∧ bn.body.s = bn.header.s
-- [p.14–15 z_t & same-slot; p.27 consistency constraints]

/-- Abstract view a node has of the tree and pool. -/
structure View (Message : Type u) (Hash : Type v) (Signature : Type w) : Type (max u (max v (max w 1))) where
  pool     : Pool Hash
  headers  : Finset (Header Hash)
  parentRel :
    ∀ {p c}, p ∈ headers → c ∈ headers →
      (BlockNode.isParentOf (Hash:=Hash) p c ∨ True) -- to be refined with actual edges
-- [pp.21–27, 31–37: algorithms over known parents/headers and pool]
end Alpenglow
