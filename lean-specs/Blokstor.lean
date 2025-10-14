/-
  Alpenglow Blokstor
  ===================

  Ground truth reference: white-paper-origintal.pdf
  - Definition 10 (Blokstor): page 19
    • Admission checks on received shred (s, t, i, z_t, r_t, (d_i, π_i), σ_t)
      1) no shred stored yet at key (s, t, i),
      2) (d_i, π_i) is a valid path/witness for Merkle root r_t at index i,
      3) σ_t is the signature of Slice(s, t, z_t, r_t) by leader(s).
    • Protocol: “Blokstor emits the event Block(slot(b), hash(b), hash(parent(b)))
      as input for Algorithm 1 when it receives the first complete block b for slot(b).”
    • Repair (Section 2.8): Blokstor may additionally collect/store another block b;
      if a block is finalized (Def. 14) only that block is stored; otherwise, before
      SafeToNotar(slot(b), hash(b)) (Def. 16) is emitted, b must be stored.

  This module formalizes the admission checks and the emitted event content from
  Definition 10. We keep the cryptographic predicates abstract via the configuration
  record, and we expose the “first complete block” event required by Algorithm 1.
  Storage and timing obligations tied to Repair/SafeToNotar are orchestrated by
  higher-level modules (Pool/Protocol) and are referenced here for completeness.
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
-- [white-paper-origintal.pdf p.19, Def. 10: emitted event structure]

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
-- [white-paper-origintal.pdf p.19, Def. 10: admission criteria bullets (1)–(3)]

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
-- [white-paper-origintal.pdf p.19, Def. 10 Protocol: Block(slot(b), hash(b), hash(parent(b)))]

end Blokstor

end Alpenglow
