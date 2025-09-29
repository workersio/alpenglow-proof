# Alpenglow TLA+ Specification Audit — Summary

This audit cross-checked every TLA+ module in `specs/` against the Alpenglow whitepaper and captured coverage, reasoning, and alignment with the paper’s claims. File and line references are provided for both spec and the whitepaper (`alpenglow-whitepaper.md`).

## Scope and Inputs

- Spec files audited: `specs/Blocks.tla`, `specs/Messages.tla`, `specs/Certificates.tla`, `specs/VoteStorage.tla`, `specs/VotorCore.tla`, `specs/Rotor.tla`, `specs/MainProtocol.tla`, `specs/MC.tla`, `specs/MC.cfg`.
- Whitepaper: `alpenglow-whitepaper.md`.
- All code blocks in each module were reviewed; each identified behavior was mapped to a whitepaper definition, lemma, theorem, or algorithm wherever applicable.

## High‑Level Findings

- Safety (Theorem 1) is modeled and enforced via invariants stating finalized blocks form a single chain and equal‑slot finalization cannot conflict, consistent with whitepaper Theorem 1 at `alpenglow-whitepaper.md:930`.
- Liveness (Theorem 2) is modeled with fairness after GST and explicit window‑level progress properties, consistent with Theorem 2 at `alpenglow-whitepaper.md:1045`, with premises expressed in the spec (correct leader, no pre‑GST timeouts, post‑GST delivery) and Rotor success encoded as actions and fairness.
- Vote types, certificate thresholds (80% fast; 60% slow path), Pool multiplicity and storage rules, and fallback guards (SafeToNotar/Skip) directly mirror Definitions 11–17 and Table 5/6.
- Leader windows, ParentReady gating, and timeout schedule follow §2.7 and Definition 17 formulas; genesis and window helpers are abstracted cleanly in `Blocks.tla`.
- Rotor (§2.2) success is captured with γ out of Γ by‑bin counting and supports the PS‑P sampling scheme (§3.1) with a faithful abstraction.

The specification is precise, modular, and sticks to TLA‑appropriate abstraction. Where the paper uses parameterized local state (e.g., VotedNotar(h)), the spec cleanly replaces it with state tags plus concrete hashes witnessed via Pool queries. This is a good TLA practice that preserves semantics without over‑modeling.

## Per‑Module Coverage

### Blocks.tla

- Constants and schedule (§1.1, §2.7): `WindowSize`, `WindowLeader`, `Leader(slot)` and window helpers align with overview (§1.1) and windowed leadership (§2.7) references in file comments (e.g., specs/Blocks.tla:18, :196). Window consistency theorem: specs/Blocks.tla:214.
- Block structure (Def. 3–5): block record with `slot`, `hash`, `parent`, `leader` maps to Def. 3–5 (`alpenglow-whitepaper.md:351`, `:357`, `:363`); genesis modeled explicitly at slot 0 (specs/Blocks.tla:54–80). Collision resistance/uniqueness is documented via `UniqueBlockHashes` (Def. 4) (specs/Blocks.tla:309; whitepaper `:357`).
- Ancestry and single‑chain: `IsAncestor` and related helpers back Theorem 1 use (specs/Blocks.tla:149–189; whitepaper Theorem 1 at `:930`). Invariants `SingleChain`, `UniqueBlocksPerSlot` match the corollaries used by the main module (specs/Blocks.tla:293–307).
- Leader windows and first slot: `FirstSlotOfWindow`, `WindowSlots`, and `IsFirstSlotOfWindow` are used by ParentReady/Timeout logic (specs/Blocks.tla:200–246) per Def. 15/17 (`alpenglow-whitepaper.md:543–:546`, `:607–:609`).

Assessment: Matches paper abstractions; modeling choices (explicit genesis, self‑parent sentinel) are documented and safe for reasoning about ancestry.

### Messages.tla

- Vote/certificate message families (Def. 11; Tables 5–6): constructors for five votes and five certificates are aligned (specs/Messages.tla:62–126, :170–212), with slot‑only messages using `NoBlock` sentinel per Table 5 (`alpenglow-whitepaper.md:497`). Shape lemmas assert intended forms (specs/Messages.tla:246–271).
- Vote classification helpers (approval/skip/final) and initial‑vs‑fallback distinctions are explicit and used by Pool and Certificates (specs/Messages.tla:214–242).

Assessment: Faithful encoding; slot‑only vs block‑bound votes modeled clearly.

### Certificates.tla

- Stake map and thresholds: Σ stake, 80% fast, 60% default from Table 6 (§2.4; `alpenglow-whitepaper.md:507`) (specs/Certificates.tla:23–48, :61–83). Count‑once semantics via deduplicating validators per slot (Def. 12; `:513`) (specs/Certificates.tla:85–121).
- Certificate creation conditions/constructors: fast/notar/notar‑fallback/skip/finalization match Table 6 rows (specs/Certificates.tla:147–228, :230–268). `CanonicalizeSkipVotes` ensures determinism under skip vs skip‑fallback (Def. 12–16 interaction).
- Validation and invariants: `IsValidCertificate`, `CertificateWellFormed`, `AllCertificatesValid`, and local implication `FastPathImplication` (fast ⇒ notar) (specs/Certificates.tla:270–350, :357–392). The skip vs block‑cert mutual exclusion encoded (specs/Certificates.tla:394–405) matches the paper’s mutually exclusive outcomes narrative in §2.6.

Assessment: Complete and precise. Note on `FastPathImplication`: the paper states fast ⇒ notar in threshold terms (`alpenglow-whitepaper.md:534`), not a subset‑of votes; the spec asserts a stronger subset property (see Issues).

### VoteStorage.tla (Pool)

- Multiplicity caps (Def. 12; `:513`): one initial notar/skip, up to 3 notar‑fallback, first skip‑fallback, first final vote (specs/VoteStorage.tla:29–58, :88–118). `StoreVote` preserves multiplicity (theorem at specs/VoteStorage.tla:491–498).
- Certificate storage (Def. 13; `:520, :532`): uniqueness per type/block/slot, skip‑vs‑block exclusion (specs/VoteStorage.tla:120–165). Store‑time checks require `IsValidCertificate` and structural well‑formedness.
- Aggregators for Def. 16 (`notar(b)`, `skip(s)`, Σ notar, max notar): specs/VoteStorage.tla:176–247. These drive SafeToNotar/Skip guards (next bullet).
- Events (Def. 15–16; `:543–:571`): `ShouldEmitBlockNotarized`, `ShouldEmitParentReady`, `CanEmitSafeToNotar`, `CanEmitSafeToSkip` encode the formulas and parent‑gating (specs/VoteStorage.tla:349–408). Parent‑gating matches the “if not first slot, require notar‑fallback parent” clause (`alpenglow-whitepaper.md:556, :569`).
- Certificate generation (Def. 13) from votes, with slow‑path finalization gated by notarization presence (specs/VoteStorage.tla:249–322).

Assessment: Matches Definitions 12–16 exactly, including careful “count‑once” semantics and the SafeToSkip inequality (`alpenglow-whitepaper.md:571`).

### VotorCore.tla

- Local state (Def. 18; `alpenglow-whitepaper.md:619–:630`): state objects encoded as tags with associated hashes obtained from Pool/events (specs/VotorCore.tla:31–116). `InitValidatorState` empty state initialization matches Def. 18 (specs/VotorCore.tla:98–116).
- Algorithm 2 helpers: `TryNotar`, `TryFinal`, `TrySkipWindow`, `CheckPendingBlocks` mirror Algorithm 2 lines (specs/VotorCore.tla:138–236, :266–318). `TryFinal` guard explicitly mirrors BlockNotarized ∧ local vote ∧ ¬BadWindow (Alg. 2 L18–21; Def. 14–15).
- Algorithm 1 handlers: `HandleBlock`, `HandleTimeout`, `HandleBlockNotarized`, `HandleParentReady`, `HandleSafeToNotar`, `HandleSafeToSkip` mirror lines and semantics (specs/VotorCore.tla:320–418, :420–465). Timeout schedule computed per Definition 17 formula (`alpenglow-whitepaper.md:609`) (specs/VotorCore.tla:332–342).
- Invariants and lemmas: typing, alignment, local safety “no mix finalization and fallback” (Lemma 22) (specs/VotorCore.tla:438–520).

Assessment: Direct line‑by‑line correspondence with Algorithms 1–2 and Def. 17–18, with TLA‑appropriate abstraction for parameterized state.

### Rotor.tla

- Rotor mechanics and success (Def. 6; §2.2): γ out of Γ success expressed in set view and by‑bin view (specs/Rotor.tla:246–273). κ > 5/3 enforced (Lemma 7; `alpenglow-whitepaper.md:418`) (specs/Rotor.tla:20–39).
- PS‑P sampling (Def. 46; `alpenglow-whitepaper.md:1154`): modeled via deterministic bin counts (floor ρ·Γ), partition stub, and by‑bin assignment constraints (specs/Rotor.tla:41–190). Candidate selection and selection soundness included (specs/Rotor.tla:209–244, :286–303).
- Latency hint for “send next leader first” (Lemma 8; `:402–:406`, `:431`) captured in `NextDisseminationDelay` (specs/Rotor.tla:275–283).

Assessment: Faithful and well‑scoped. The `ResilienceOK`/stake guards are explicit modeling additions (see Issues) and are isolated to selection feasibility.

### MainProtocol.tla

- System state, Init, Next, Fairness: full protocol composition with rotor, blokstor, pool, voting, finalization (specs/MainProtocol.tla:1–220, :680–736, :746–772). Genesis bootstrapping sets ParentReady(1, genesis) by fiat to seed the first window (consistent with Def. 15) (specs/MainProtocol.tla:180–218).
- Actions: `ReceiveBlock`, `GenerateCertificateAction`, `FinalizeBlock`, delivery/broadcast, Honest/Byzantine proposal, Rotor dissemination, Repair (Algorithms and Def. 13–16, Alg. 3–4) (specs/MainProtocol.tla:220–600, :320–418, :520–620).
- Safety invariants: Theorem 1 single‑chain (`SafetyInvariant`), equal‑slot corollary (`NoConflictingFinalization`), vote uniqueness (Lemma 20; `alpenglow-whitepaper.md:820`), unique notarization (Lemma 24; `:855`), certificate non‑equivocation (Def. 13; `:520`), and skip‑vs‑block exclusion (specs/MainProtocol.tla:782–906).
- ParentReady and BlockNotarized witnesses tie state to Pool certificates (Def. 15) (specs/MainProtocol.tla:1285–1337). Timeout discipline invariants match Def. 17 (timeouts in future, local clock monotonic) (specs/MainProtocol.tla:1056–1098).
- Liveness: Basic progress after GST, fast path “one round” from fast cert, TRYFINAL progress, and window‑level liveness approximating Theorem 2 (`alpenglow-whitepaper.md:1045`) with explicit premises and fairness (specs/MainProtocol.tla:1111–1270). Bounded‑time finalization via δθ abstractions (`min(δ80%, 2δ60%)`) tracked by `avail80Start`/`avail60Start` (specs/MainProtocol.tla:1367–1410).

Assessment: Comprehensive. All major definitions, algorithms, and theorems are represented with the right abstractions and explicit assumptions.

### MC.tla / MC.cfg

- Harness config instantiates a small system and checks key invariants/properties (`Invariant`, `BasicLiveness`, `FastPathOneRound`, `WindowFinalizationAll`, etc.) (specs/MC.cfg:34–62). Stake map and window leader function provided (specs/MC.tla:10–35).

Assessment: Suitable for sanity; keeps bounded exploration while exercising both paths.

## Claims Coverage Matrix (selected highlights)

- Theorem 1 (safety): captured by `SafetyInvariant` and corollary invariants (specs/MainProtocol.tla:782–840; whitepaper `alpenglow-whitepaper.md:930`).
- Lemma 20 (one initial vote per slot): `VoteUniqueness` (specs/MainProtocol.tla:840–854; paper `:820`).
- Lemma 24 (unique notarization per slot): `UniqueNotarization` (specs/MainProtocol.tla:854–874; paper `:855`).
- Def. 15 (ParentReady/BlockNotarized): event emission and state witnesses (specs/VoteStorage.tla:354–372, :340–347; specs/MainProtocol.tla:1265–1305; paper `:543–:546`).
- Def. 16 (SafeToNotar/Skip): explicit guards (specs/VoteStorage.tla:374–415; paper `:554–:571`).
- Def. 17 (timeouts): schedule and invariants (specs/VotorCore.tla:332–342; specs/MainProtocol.tla:1085–1098; paper `:607–:613`).
- Theorem 2 (liveness): window‑level liveness and fairness after GST (specs/MainProtocol.tla:1206–1267; paper `:1045`).
- 20+20 resilience: stake assumptions/invariants enforce <20% Byzantine, <=20% unresponsive (specs/MainProtocol.tla:136–167, :1426–1442; paper `:107`, `:121`).

## TLA+ Best‑Practice Notes

- Parameterized local state (e.g., VotedNotar(h)) replaced by state tags plus Pool queries (e.g., `VotedForBlock`) to avoid embedding hashes into state — improves tractability and matches algorithm intent.
- Slot‑only vs block‑bound votes are strongly typed using `NoBlock`, with lemmas asserting shapes for model checking.
- Stake aggregation enforces “count once per slot” by deduplication — a common pitfall handled carefully here.
- Safety proofs are represented as invariants; liveness ties to fairness after GST and explicit premises.

## Conclusion

- The TLA+ specification implements the whitepaper’s definitions, algorithms, and theorems with appropriate abstraction. Safety is encoded as invariants consistent with Theorem 1, and liveness is captured with fairness and window assumptions consistent with Theorem 2.
- Minor specification‑level additions are clearly marked (e.g., Rotor resilience guards, genesis sentinel discipline). Open questions and suggested tweaks are detailed in `issues_openai.md` with precise references.

