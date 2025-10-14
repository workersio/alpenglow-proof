import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Alpenglow

universe u v w x

-- Natural-number indices as in Defs. 1–3 (p.14–15)
abbrev Slot := Nat         -- s
abbrev SliceIndex := Nat   -- t
abbrev ShredIndex := Nat   -- i

/-– Merkle opening (Section 1.6): (d_i, π_i) under a Merkle root. -/
structure MerkleWitness (Data : Type u) (Path : Type v) where
  d  : Data
  π  : Path
  deriving Repr

namespace Merkle

/-– Merkle algebra (Section 1.6): leaf labeling, branching, and ⊥ padding. -/
structure Hasher (Hash : Type u) where
  leafLabel : Hash → Hash
  branch    : Hash → Hash → Hash
  padding   : Hash

variable {Hash : Type u} (H : Hasher Hash)

/-- Next power of two ≥ n (complete full tree; Def. 4, p.15). -/
def nextPow2AtLeast : Nat → Nat
  | 0     => 1
  | n+1   =>
    let m := nextPow2AtLeast n
    if n+1 ≤ m then m else m * 2

/-- Pad leaves with ⊥ to a power of two (Def. 4, p.15). -/
@[simp]
def padLeavesToPow2 (xs : List Hash) : List Hash :=
  let k := xs.length
  let m := nextPow2AtLeast k
  let base := xs.map H.leafLabel
  let pad  := H.leafLabel H.padding
  base ++ List.replicate (m - k) pad

/-– One Merkle level (pairwise branch; odd tail passes through). -/
@[simp] def level : List Hash → List Hash
  | []             => []
  | [x]            => [x]
  | x :: y :: rest => H.branch x y :: level rest

/-- Fuelled fold-up to the root. Returns `none` if fuel is exhausted.
    With leaves padded to a power of two, using `leaves.length` as fuel
    is sufficient, so `none` should be unreachable in `root`. -/
def rootAux : Nat → List Hash → Option Hash
  | _, []                      => some (H.leafLabel H.padding)
  | _, [x]                     => some x
  | 0, _ :: _ :: _             => none
  | Nat.succ fuel, xs@(_::_::_) => rootAux fuel (level H xs)

/-- Block/slice root = Merkle root of padded leaves (Defs. 2 & 4, p.14–15). -/
def root (xs : List Hash) : Hash :=
  let leaves := padLeavesToPow2 H xs
  match rootAux H leaves.length leaves with
  | some r => r
  | none   => H.leafLabel H.padding   -- Unreachable if fuel is sufficient

end Merkle

/-- Definition 1 (shred), §2.1, p.14.
    Tuple: (s, t, i, z_t, r_t, (d_i, π_i), σ_t)
    - s: slot, t: slice index, i: shred index (all ∈ ℕ)
    - z: last-slice flag z_t ∈ {0,1}
    - r: Merkle root r_t of the slice
    - witness: (d_i, π_i) opening under r_t (Section 1.6)
    - sigma: signature σ_t on Slice(s, t, z_t, r_t) by leader(s)
-/
structure Shred (Data : Type u) (Path : Type v) (Hash : Type w)
    (Signature : Type x) where
  s : Slot
  t : SliceIndex
  i : ShredIndex
  z : Bool
  r : Hash
  witness : MerkleWitness Data Path  -- (d_i, π_i)
  sigma : Signature
  deriving Repr

/-- Definition 2 (slice), §2.1, p.14: (s, t, z_t, r_t, M_t, σ_t). -/
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

/-- Header part of a slice: Slice(s, t, z_t, r_t) (p.14). -/
def header (sl : Slice Message Hash Signature) :
    Slot × SliceIndex × Bool × Hash :=
  (sl.s, sl.t, sl.z, sl.r)
end Slice

/-- Definition 3 (block), §2.1, p.14–15.
    A block is the sequence of all slices in a slot s with terminal flag z_k = 1
    and z_t = 0 for t < k. The block data is the concatenation of slice payloads.
-/
structure Block (Message : Type u) (Hash : Type v) (Signature : Type w) where
  s : Slot
  slices : List (Slice Message Hash Signature)
  deriving Repr

namespace Block

variable {Message : Type u} {Hash : Type v} {Signature : Type w}

@[simp] def sliceCount (b : Block Message Hash Signature) : Nat :=
  b.slices.length

def lastSlice?
    (b : Block Message Hash Signature) :
    Option (Slice Message Hash Signature) :=
  b.slices.getLast?

def data (b : Block Message Hash Signature) : List Message :=
  b.slices.map (·.M)

def sliceRoots (b : Block Message Hash Signature) : List Hash :=
  b.slices.map (·.r)

/-– Definition 4 (block hash), §2.1, p.15: Merkle root over slice roots padded
    to the next power-of-two leaves (first k leaves r₁..r_k labeled as leaves; rest ⊥). -/
def hash (b : Block Message Hash Signature) (H : Merkle.Hasher Hash) : Hash :=
  Merkle.root H (b.sliceRoots)

def hasTerminalSlice (b : Block Message Hash Signature) : Prop :=
  match b.lastSlice? with
  | some sl => sl.z = true
  | none    => False

def allSlicesInSlot (b : Block Message Hash Signature) : Prop :=
  ∀ sl, sl ∈ b.slices → sl.s = b.s

/-- Block validity per Def. 3 (p.14–15): nonempty; all slices in slot;
    terminal slice has z = 1; all earlier slices have z = 0. -/
def valid (b : Block Message Hash Signature) : Prop :=
  b.slices ≠ [] ∧
  b.allSlicesInSlot ∧
  b.hasTerminalSlice ∧
  ∀ sl, sl ∈ b.slices.dropLast → sl.z = false

end Block

/-– Node identifier (proof-of-stake node id). -/
abbrev NodeId := Nat

/-– Signature scheme placeholder (Section 1.6: aggregate signatures on p.12). -/
class SigScheme (Signature : Type*) (Hash : Type*) (NodeId : Type*) where
  verify : NodeId → Hash → Signature → Prop

/-– Block identifier equals block hash (Def. 4). -/
abbrev BlockId (Hash : Type _) := Hash

/-– Block header capturing (slot, parent pointer, id = hash(b)); parent chain per Def. 5 (p.15). -/
structure Header (Hash : Type _) where
  s        : Slot
  parentId : Option Hash
  id       : Hash
  deriving DecidableEq

/-– Coupling of header and body (same slot), cf. Defs. 3–5. -/
structure BlockNode
    (Message : Type u) (Hash : Type v) (Signature : Type w) where
  header : Header Hash
  body   : Block Message Hash Signature

namespace BlockNode

/-– Parent relation: c.parentId = p.id and p.s < c.s (Def. 5, p.15). -/
def isParentOf (p c : Header Hash) : Prop :=
  c.parentId = some p.id ∧ p.s < c.s

/-– Ancestor/descendant closure over parent links (Def. 5, p.15). -/
inductive IsAncestor (root : Header Hash) : Header Hash → Prop
| refl  : IsAncestor root root
| step  : ∀ {mid child}, IsAncestor root mid → isParentOf (Hash:=Hash) mid child → IsAncestor root child

def IsDescendant (child root : Header Hash) : Prop := IsAncestor (Hash:=Hash) root child

end BlockNode

/-- Stake model placeholder; weights drive thresholds (Assumption 1, p.4). -/
structure StakeProfile where
  N      : Nat
  weight : NodeId → Nat

def Correct := NodeId → Prop

structure AdversaryBound (SP : StakeProfile) (correct : Correct) where
  byzStakeBounded : Prop

namespace StakeProfile

/-- All node identifiers are assumed to be enumerated as `0, 1, ..., N-1`. -/
@[simp] def allNodes (sp : StakeProfile) : Finset NodeId :=
  Finset.range sp.N

/-- Total stake over all nodes `0..N-1`. -/
@[simp] def totalStake (sp : StakeProfile) : Nat :=
  Finset.sum sp.allNodes sp.weight

/-- Stake weight of a given voter set. -/
@[simp] def weightOf (sp : StakeProfile) (voters : Finset NodeId) : Nat :=
  Finset.sum (voters ∩ sp.allNodes) sp.weight

/-- Threshold check: voted/total ≥ num/den (with `den ≠ 0`). -/
def meetsFraction (sp : StakeProfile) (voters : Finset NodeId)
    (num den : Nat) : Prop :=
  den ≠ 0 ∧ (weightOf sp voters) * den ≥ num * (totalStake sp)

end StakeProfile

inductive VoteType | notar | notarFallback | skip | skipFallback | final
deriving DecidableEq, Repr

/-– Vote keys (Table 5, §2.4, p.19): slot-scoped (Skip/Final) and block-scoped (Notar). -/
inductive VoteKey (Hash : Type _)
| slot  : Slot → VoteKey Hash
| block : Slot → BlockId Hash → VoteKey Hash
deriving DecidableEq, Repr

/-– Voting message (Table 5, §2.4, p.19). -/
structure Vote (Hash : Type _) (Signature : Type _) where
  voter : NodeId
  kind  : VoteType
  key   : VoteKey Hash
  sig   : Signature

/-– Certificate (Table 6, §2.4, p.20): aggregation of votes for a key.
    `kind` denotes the underlying aggregated vote type; thresholds (e.g., 80% fast vs. 60%)
    are captured via `thrOK` and by usage in Def. 14.
    Note: The whitepaper includes aggregate signatures for certificates (Section 1.6).
    We intentionally omit the aggregate signature field here to keep `Basics` focused on
    structural definitions; cryptographic details can be modeled via `SigScheme` in higher layers. -/

structure Certificate (Hash : Type _) where
  kind      : VoteType
  key       : VoteKey Hash
  voters    : Finset NodeId
  weightSum : Nat
  thrOK     : Prop   -- “≥ 80%” for fast-finalization; “≥ 60%” otherwise (Table 6)

abbrev NotarCert   (Hash : Type _) := Certificate Hash
abbrev SkipCert    (Hash : Type _) := Certificate Hash
abbrev FinalCert   (Hash : Type _) := Certificate Hash

/-– Pool (Defs. 12–13, §2.5, p.20–21): storage for votes and certificates per (type,key). -/
structure Pool (Hash : Type v) : Type (max 1 v) where
  votes : VoteType → VoteKey Hash → Finset NodeId
  certs : VoteType → VoteKey Hash → Option (Certificate Hash)

namespace Pool

variable {Hash : Type v}

/-– Notarization certificate lookup (Table 6). -/
def notarCert? (P : Pool Hash) (s : Slot) (b : BlockId Hash) :
    Option (NotarCert Hash) :=
  P.certs VoteType.notar (VoteKey.block s b)

def skipCert? (P : Pool Hash) (s : Slot) : Option (SkipCert Hash) :=
  P.certs VoteType.skip (VoteKey.slot s)

def finalCert? (P : Pool Hash) (s : Slot) :
    Option (FinalCert Hash) :=
  P.certs VoteType.final (VoteKey.slot s)

/-- Fast-finalization (Def. 14, §2.4/§2.6): notar certificate satisfying the 80% threshold. -/
def fastFinalCert (P : Pool Hash) (s : Slot) (b : BlockId Hash) : Prop :=
  ∃ C, P.notarCert? s b = some C ∧ C.thrOK

end Pool

/-– Events (Defs. 15–16, §2.4–§2.6, p.21–22). -/
inductive Event (Hash : Type _)
| BlockNotarized  (s : Slot) (b : BlockId Hash)
| ParentReady     (s : Slot) (parent : BlockId Hash)
| SafeToNotar     (s : Slot) (b : BlockId Hash)
| SafeToSkip      (s : Slot)
deriving Repr, DecidableEq

/-– Leader schedule mapping slots to leaders (overview §1.1, §2.7). -/
abbrev LeaderSchedule := Slot → NodeId

/-– Leader window: consecutive slots led by the same leader (overview §1.1). -/
structure LeaderWindow where
  slots    : List Slot
  nonempty : slots ≠ []
  deriving Repr

/-– Schedule bundles leader mapping and leader windows. -/
structure Schedule where
  leader : LeaderSchedule
  window : Slot → LeaderWindow

/-– Notarized(h): Pool holds a notarization certificate for h (Table 6). -/
def Notarized (P : Pool Hash) (h : Header Hash) : Prop :=
  ∃ C, P.notarCert? h.s h.id = some C

/-- Finalization (Def. 14, §2.4/§2.6): fast (80%) or slow (final cert + notar cert). -/
def hasFinalCert (P : Pool Hash) (s : Slot) : Prop :=
  ∃ C, P.finalCert? s = some C
def hasNotarCert (P : Pool Hash) (s : Slot) (b : BlockId Hash) : Prop :=
  ∃ C, P.notarCert? s b = some C

/-– Finalized per Def. 14: either via fast-finalization (80% notar votes) or via
    slow path (finalization cert on slot + notarization cert for the unique block). -/
inductive Finalized (P : Pool Hash) (h : Header Hash) : Prop
| fast : P.fastFinalCert (Hash:=Hash) h.s h.id → Finalized P h
| slow : hasFinalCert (Hash:=Hash) P h.s → hasNotarCert (Hash:=Hash) P h.s h.id → Finalized P h


def SlotLe (a b : Header Hash) : Prop := a.s ≤ b.s

/-– Block/body matches header slot and satisfies Def. 3 invariants. -/
def WellFormed (bn : BlockNode Message Hash Signature) : Prop :=
  bn.body.valid ∧ bn.body.s = bn.header.s

/-– Keep only headers closed under parent links (Def. 5, p.15). -/
structure View (Message : Type u) (Hash : Type v) (Signature : Type w) : Type (max u (max v (max w 1))) where
  pool    : Pool Hash
  headers : Finset (Header Hash)
  closedUnderParents :
    ∀ {c pid}, c ∈ headers → c.parentId = some pid →
      ∃ p, p ∈ headers ∧ p.id = pid ∧ p.s < c.s

end Alpenglow
