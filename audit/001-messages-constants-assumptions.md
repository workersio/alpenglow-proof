# Audit: Messages.tla Constants and Assumptions

- File: `specs/tla/alpenglow/Messages.tla:16`
- Scope: foundational constants and typing assumptions used across message, certificate, and protocol modules

## 1. Code Being Audited

```tla
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
```

## 2. Whitepaper Sections and References Represented

- Slots as natural numbers
  - `alpenglow-whitepaper.md:213` (Slot: “Each epoch is partitioned into slots. A slot is a natural number...”) 
  - `alpenglow-whitepaper.md:53` (Time is partitioned into slots; leader windows)
- Validators (nodes) exist and are known
  - `alpenglow-whitepaper.md:194` (Nodes/validators, public keys, known set during an epoch)
- Block hashes exist and are derived from a collision-resistant hash
  - `alpenglow-whitepaper.md:259` (Hash function)
- Skip vs. block-carrying votes (necessitating a sentinel value for “no block”)
  - `alpenglow-whitepaper.md:245` (For every slot, either finalize some block or yield a skip)
  - `alpenglow-whitepaper.md:478` (Definition 11: message types), `alpenglow-whitepaper.md:497` (Table 5: voting messages), `alpenglow-whitepaper.md:507` (Table 6: certificate messages)
- Leader windows and slot arithmetic (motivates prefix-closed `Slots` domain used by later helpers like window calculations)
  - `alpenglow-whitepaper.md:215`–`alpenglow-whitepaper.md:222` (Leader, leader window, schedule)

## 3. Reasoning: What The Code Encodes vs. Whitepaper Claims

- Validators
  - Code requires `Validators # {}` establishing a non-empty validator set. The whitepaper models an epoch with a known set of nodes/validators (`n` nodes), consistent with a non-empty set.
- Slots
  - `Slots ⊆ Nat` and prefix-closure `∀ s ∈ Slots: 0..s ⊆ Slots` model slots as natural numbers and enable safe use of ranges/arithmetic over slots (e.g., window functions, historical lookups). Whitepaper explicitly defines slots as natural numbers and uses ranges and prior-slot reasoning throughout. Prefix-closure is a standard TLA+ modeling convenience that matches the paper’s use of slot intervals and predecessor reasoning.
- BlockHashes
  - `BlockHashes # {}` ensures at least one possible hash, aligning with the presence of a collision-resistant hash function. It provides a typed universe for block identifiers used across votes and certificates.
- NoBlock sentinel
  - `NoBlock ∉ BlockHashes` cleanly separates “skip/no block” cases from real blocks. The paper’s message taxonomy includes votes without an associated block (skip/finalization messages in Table 5) and certificates for skip/finalization (Table 6). Using a distinct sentinel in the type system is a faithful abstraction to model those cases without conflating them with actual block identifiers.
- Genesis and slot zero
  - While not in this snippet, `specs/tla/alpenglow/Blocks.tla:29` adds `0 ∈ Slots` as a modeling choice for genesis. This is compatible with the whitepaper (which indexes `s = 1..L`) and is a benign abstraction detail.

## 4. Cross-Module References (Context Consumers)

These constants and assumptions are imported and relied upon across the TLA specifications. Representative references:

- Messages typing and helpers
  - `specs/tla/alpenglow/Messages.tla:55`–`specs/tla/alpenglow/Messages.tla:57` (vote fields typed by `Validators`, `Slots`, `BlockHashes ∪ {NoBlock}`)
  - `specs/tla/alpenglow/Messages.tla:165`–`specs/tla/alpenglow/Messages.tla:168` (`IsValidVote` rules about `BlockHashes` vs. `NoBlock`)
- Certificates typing and predicates
  - `specs/tla/alpenglow/Certificates.tla:283`–`specs/tla/alpenglow/Certificates.tla:295` (certificate fields typed by `Slots`, `BlockHashes ∪ {NoBlock}`)
  - `specs/tla/alpenglow/Certificates.tla:277`, `specs/tla/alpenglow/Certificates.tla:312`–`specs/tla/alpenglow/Certificates.tla:314` (explicit usage of `NoBlock` for skip/final types)
- Validator local state (Votor core)
  - `specs/tla/alpenglow/VotorCore.tla:56`–`specs/tla/alpenglow/VotorCore.tla:62` (per-slot maps typed by `Slots`; `parentReady` over `BlockHashes ∪ {NoBlock}`)
  - `specs/tla/alpenglow/VotorCore.tla:325`–`specs/tla/alpenglow/VotorCore.tla:331` (validator record typing constraints)
- Blocks and leader windows
  - `specs/tla/alpenglow/Blocks.tla:21`–`specs/tla/alpenglow/Blocks.tla:29` (genesis assumptions, `0 ∈ Slots`)
  - `specs/tla/alpenglow/Blocks.tla:221`–`specs/tla/alpenglow/Blocks.tla:222` (theorem relying on slot-domain sanity enabled by prefix-closure)
- Vote storage and Pool
  - `specs/tla/alpenglow/VoteStorage.tla:25`–`specs/tla/alpenglow/VoteStorage.tla:33` (Pool maps keyed by `Slots` and `Validators`)

These usages demonstrate that the audited assumptions are the foundational typing and domain constraints enabling later modules to be well-typed and to perform slot arithmetic and case distinctions on “block vs no-block”.

## 5. Conclusion of the Audit

- Correctness vs. whitepaper: The constants and accompanying assumptions faithfully model the whitepaper’s abstractions for nodes/validators, slots as natural numbers, block identifiers, and the existence of skip/finalization messages that do not reference a block. The separation of `NoBlock` from `BlockHashes` matches the paper’s message tables and avoids ambiguity in the type system.
- Adequacy for later reasoning: Prefix-closure of `Slots` is sufficient to support window and predecessor-slot reasoning used throughout, and is leveraged explicitly in Blocks-related lemmas. The assumptions are minimal, composable, and align with the separate genesis modeling choice in `Blocks.tla`.

Overall, the snippet is consistent with the whitepaper and supports the intended abstractions across the spec.

## 6. Open Questions or Concerns

- Non-empty `Slots`
  - The snippet does not assert `Slots # {}`. While many modules add stronger assumptions (e.g., `Blocks.tla:29` enforces `0 ∈ Slots`), using `Messages.tla` in isolation would allow the degenerate `Slots = {}`. This is typically harmless for safety properties but may obscure liveness reasoning. If `Messages.tla` is ever used standalone, consider stating non-emptiness.
- Epoch boundedness
  - The whitepaper reasons over an epoch length `L` (finite). Other modules introduce constructs like `MaxSlot` (e.g., `specs/tla/alpenglow/MainProtocol.tla:605`). If needed, one could optionally bound `Slots ⊆ 0..MaxSlot` at the top-level to match the epoch-bounded model more directly.
- Explicit link to whitepaper numbering
  - While comments in `Messages.tla` already mention §2.4 and Def. 11/Tables 5–6, adding a brief note near the `NoBlock` sentinel to tie its use specifically to skip/finalization message types (Table 5) can aid future readers.

## 7. Suggestions for Improvement

- Add a (commented) optional assumption for non-empty slots at an integration module:
  - Example (not necessarily in `Messages.tla`): `ASSUME Slots # {}` or `ASSUME 0 ∈ Slots` if genesis modeling is desired globally.
- Centralize epoch bound (if applicable) so all modules agree on slot domain limits:
  - Define `MaxSlot` once and use `Slots == 0..MaxSlot` in a top-level spec, making finite model assumptions explicit and consistent with the whitepaper’s epoch framing.
- Document `NoBlock` in module header comments:
  - One sentence connecting `NoBlock` to skip/finalization vote/certificate lines in Table 5/6 (whitepaper lines `497`, `507`) to strengthen traceability.

---
Prepared by: TLA+ audit of foundational constants and assumptions in `Messages.tla`.
