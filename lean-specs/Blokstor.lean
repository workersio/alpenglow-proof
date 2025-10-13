/-
  Alpenglow Blokstor

  This module formalizes Definition 10 (“Blokstor”) from the Alpenglow
  whitepaper [p.19].  The Blokstor is the data structure responsible for
  ingesting shreds produced by Rotor, enforcing the authenticity checks
  spelled out in the definition, and materializing the first complete block
  that arrives for each slot.  When such a block is assembled, Blokstor
  produces the `Block` event containing the slot, the block hash, and the
  hash of its parent as described in the whitepaper.
-/

import Basics

namespace Alpenglow

universe u v w x y

/-- The event emitted by Blokstor once a slot's first complete block has
    been reconstructed.  The payload matches the triple
    `Block(slot(b), hash(b), hash(parent(b)))` from the whitepaper. -/
structure BlockEvent (Hash : Type u) where
  slot : Slot
  hash : Hash
  parentHash : Hash
  deriving Repr
-- [p.19, Def. 10: emitted event structure]

/--
  Configuration data describing how Blokstor validates shreds and extracts
  parent information from blocks.  The predicates abstract over concrete
  cryptographic checks so that the formalization can remain agnostic of the
  underlying implementations.
-/
structure BlokstorConfig
    (Data : Type u) (Path : Type v) (Message : Type w)
    (Hash : Type x) (Signature : Type y) where
  /-- The Merkle hasher used to compute `hash(b)` for completed blocks. -/
  hasher : Merkle.Hasher Hash
  /-- Predicate witnessing that a shred's Merkle data `(d_i, π_i)` is valid
      for the slice root contained in the shred. -/
  validWitness : Shred Data Path Hash Signature → Prop
  /-- Predicate capturing that the shred's signature is the leader's
      signature over the slice header `(s, t, z_t, r_t)`. -/
  signedSlice : Shred Data Path Hash Signature → Prop
  /-- Extracts the hash of the parent block from the decoded block data. -/
  parentHash : Block Message Hash Signature → Hash

namespace BlokstorConfig

end BlokstorConfig

/--
  Blokstor state together with the invariants mandated by Definition 10.
  The structure records

  * the shreds stored for each slot/slice/shred index triple,
  * the first complete block reconstructed for every slot, and
  * well-formedness guarantees mirroring the acceptance checks performed
    when new shreds arrive.
-/
structure Blokstor
    {Data : Type u} {Path : Type v} {Message : Type w}
    {Hash : Type x} {Signature : Type y}
    (cfg : BlokstorConfig Data Path Message Hash Signature) where
  /-- Partial map of stored shreds keyed by `(slot, slice, shred)` indices. -/
  stored :
      Slot → SliceIndex → ShredIndex →
        Option (Shred Data Path Hash Signature)
  /-- The first complete block received for each slot, if any. -/
  firstComplete : Slot → Option (Block Message Hash Signature)
  /-- Stored shreds respect their key indices. -/
  indices_consistent :
      ∀ {s t i} {sh : Shred Data Path Hash Signature},
        stored s t i = some sh →
          sh.s = s ∧ sh.t = t ∧ sh.i = i
  /-- Every stored shred passed the Merkle witness check. -/
  witness_ok :
      ∀ {s t i} {sh : Shred Data Path Hash Signature},
        stored s t i = some sh →
          cfg.validWitness sh
  /-- Every stored shred carries the leader's signature over its slice header. -/
  signature_ok :
      ∀ {s t i} {sh : Shred Data Path Hash Signature},
        stored s t i = some sh →
          cfg.signedSlice sh
  /-- Each reconstructed block is the first complete block for its slot and
      satisfies the well-formedness predicate from Definition 3. -/
  firstComplete_valid :
      ∀ {s} {b : Block Message Hash Signature},
        firstComplete s = some b →
          b.s = s ∧ Block.valid b

namespace Blokstor

variable {Data : Type u} {Path : Type v} {Message : Type w}
variable {Hash : Type x} {Signature : Type y}
variable {cfg : BlokstorConfig Data Path Message Hash Signature}

/-- Condition under which Blokstor may ingest a new shred.  The shred must
    not have been stored under the same `(s, t, i)` key yet and it must
    satisfy the Merkle and signature predicates from Definition 10. -/
def canInsert
    (bs : Blokstor cfg) (sh : Shred Data Path Hash Signature) : Prop :=
  bs.stored sh.s sh.t sh.i = none ∧
    cfg.validWitness sh ∧
    cfg.signedSlice sh
-- [p.19, Def. 10: admission criteria for shreds]

/--
  The `Block` event emitted for a slot, if Blokstor reconstructed the first
  complete block for that slot.  This packages the information required by
  Algorithm 1 in the whitepaper.
-/
def eventForSlot (bs : Blokstor cfg) (s : Slot) :
    Option (BlockEvent Hash) :=
  (bs.firstComplete s).map fun b =>
    { slot := s
      hash := Block.hash b cfg.hasher
      parentHash := cfg.parentHash b }
-- [p.19, Def. 10: event content]

end Blokstor

end Alpenglow
