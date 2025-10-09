/-
  Alpenglow Proof Basics

  This module collects the core data structures shared across the Lean
  formalization of the Alpenglow protocol.  In particular we capture
  the whitepaper definitions for shreds, slices, and blocks so that the
  subsequent lemmas can refer to a single source of truth.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace Alpenglow

universe u v w x

/-- Slots, slice indices, and shred indices are natural numbers in the formalization,
    matching the whitepaper's notation. -/
abbrev Slot := Nat
abbrev SliceIndex := Nat
abbrev ShredIndex := Nat

/-- A helper object bundling shred payload and its Merkle path `(d_i, π_i)`. -/
structure MerkleWitness (Data : Type u) (Path : Type v) where
  d : Data
  pi : Path
  deriving Repr

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

variable {Hash : Type u} (H : Hasher Hash)

/-- Combine a level of Merkle leaves pairwise, duplicating the final element if
    necessary so the resulting list has half the length (rounded up). -/
def level (xs : List Hash) : List Hash :=
  match xs with
  | [] => []
  | [x] => [H.branch (H.leafLabel x) (H.leafLabel x)]
  | x :: y :: rest =>
      H.branch (H.leafLabel x) (H.leafLabel y) :: level rest

/-- Recursively compute a Merkle root with an explicit fuel argument to ensure
    structural termination in Lean. The fuel is typically the length of the
    input list. -/
def rootAux : Nat → List Hash → Hash
  | _, [] => H.leafLabel H.padding
  | _, [x] => H.leafLabel x
  | 0, _ :: _ :: _ => H.leafLabel H.padding
  | Nat.succ fuel, xs@(_ :: _ :: _) =>
      rootAux fuel (level H xs)

/-- Compute the Merkle root for an arbitrary list of leaf hashes.
    The algorithm follows the whitepaper description:
    - Leaves are labelled via `leafLabel`
    - Pairs of leaves are combined with `branch`
    - If the number of leaves is odd, the final leaf is duplicated to maintain a
      full binary tree (equivalently, padding up to the next power of two). -/
def root (xs : List Hash) : Hash :=
  rootAux H xs.length xs

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

/-- Definition 2 (slice) from the whitepaper. -/
structure Slice (Message : Type u) (Hash : Type v) (Signature : Type w) where
  s : Slot
  t : SliceIndex
  z : Bool
  r : Hash
  M : Message
  sigma : Signature
  deriving Repr

namespace Slice

variable {Message : Type u} {Hash : Type v} {Signature : Type w}

/-- Convenience: the metadata tuple `(s, t, z_t, r_t)` of a slice. -/
def header (sl : Slice Message Hash Signature) :
    Slot × SliceIndex × Bool × Hash :=
  (sl.s, sl.t, sl.z, sl.r)

end Slice

/-! We write `k = b.sliceCount` to mirror the notation in Definition 3. -/
/-- Definition 3 (block) from the whitepaper.  A block is a sequence of slices
    that all belong to the same slot. -/
structure Block (Message : Type u) (Hash : Type v) (Signature : Type w) where
  s : Slot
  slices : List (Slice Message Hash Signature)
  deriving Repr

namespace Block

variable {Message : Type u} {Hash : Type v} {Signature : Type w}

/-- Number of slices stored in the block. -/
@[simp]
def sliceCount (b : Block Message Hash Signature) : Nat :=
  b.slices.length

/-- Optional access to the last slice of the block. -/
def lastSlice?
    (b : Block Message Hash Signature) :
    Option (Slice Message Hash Signature) :=
  b.slices.getLast?

/-- Extract the decoded slice data for the block. -/
def data (b : Block Message Hash Signature) : List Message :=
  b.slices.map (·.M)

/-- Extract the Merkle roots from each slice. -/
def sliceRoots (b : Block Message Hash Signature) : List Hash :=
  b.slices.map (·.r)

/-- Definition 4 (block hash).  The block hash is the root of the complete
    Merkle tree obtained from the slice roots `r_t`. -/
def hash (b : Block Message Hash Signature) (H : Merkle.Hasher Hash) : Hash :=
  Merkle.root H (b.sliceRoots)

/-- Checks that the block contains a designated terminal slice. -/
def hasTerminalSlice (b : Block Message Hash Signature) : Prop :=
  match b.lastSlice? with
  | some sl => sl.z = true
  | none => False

/-- Predicate stating that every slice in the block belongs to the same slot. -/
def allSlicesInSlot (b : Block Message Hash Signature) : Prop :=
  ∀ {sl}, sl ∈ b.slices → sl.s = b.s

/-- Helper predicate capturing the typical well-formedness conditions mentioned
    in the whitepaper: slices belong to the same slot and the terminal slice is
    marked with `z_t = 1`.  Further constraints (e.g. bounds on size) can be
    layered on top as needed by the proofs. -/
def valid (b : Block Message Hash Signature) : Prop :=
  (b.slices ≠ []) ∧
    b.allSlicesInSlot ∧
    b.hasTerminalSlice ∧
    ∀ {sl}, sl ∈ b.slices.dropLast → sl.z = false

end Block

end Alpenglow
