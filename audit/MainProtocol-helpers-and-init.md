**Code Under Audit**

- Module: `specs/tla/alpenglow/MainProtocol.tla`
- Scope: Constants, state variables, helper predicates, and Init
  - Header and EXTENDS: `specs/tla/alpenglow/MainProtocol.tla:1`
  - Constants and assumptions: `specs/tla/alpenglow/MainProtocol.tla:22`
  - State variables and tuple `vars`: `specs/tla/alpenglow/MainProtocol.tla:41`
  - Helper predicates: `specs/tla/alpenglow/MainProtocol.tla:56`
    - `CorrectNodes == Validators \ byzantineNodes`
    - `RotorCorrectRelays(relays) == relays \cap CorrectNodes`
    - `EnoughCorrectRelays(relays) == Cardinality(relays \cap CorrectNodes) >= GammaDataShreds`
    - `NeedsBlockRepair(pool, block) == HasNotarizationCert(pool, block.slot, block.hash) \/ HasNotarFallbackCert(pool, block.slot, block.hash)`
    - `AfterGST == time >= GST`
    - `ByzantineStake == CalculateStake(byzantineNodes)`
    - `ByzantineStakeOK == ByzantineStake * 100 < TotalStake * 20`
  - Initial state `Init`: `specs/tla/alpenglow/MainProtocol.tla:87`
    - Initializes each validator with `InitValidatorState`, sets `parentReady[1] = GenesisHash`, and adds state `"ParentReady"` for slot 1; sets `blocks = {GenesisBlock}`, empty `messages`, picks `byzantineNodes` of size `ByzantineCount`, requires `ByzantineStakeOK`, sets `time = 0`, `finalized[v] = {}`, and `blockAvailability[v] = {GenesisBlock}`.

**Whitepaper References**

- Assumption 1 (fault tolerance): Byzantine stake < 20%
  - alpenglow-whitepaper.md:107
- Partial synchrony and GST: model and fairness premises
  - alpenglow-whitepaper.md:105, and §2.10
- Rotor success condition (Definition 6): leader correct and ≥ γ correct relays
  - alpenglow-whitepaper.md:414–416
- Pool and certificates (Definitions 11–16): events and thresholds; ParentReady and BlockNotarized
  - alpenglow-whitepaper.md:543–569
- Repair trigger and procedure (Section 2.8, Definition 19, Algorithm 4)
  - alpenglow-whitepaper.md:778–840
- Blocks and ancestry (Definitions 3–5)
  - alpenglow-whitepaper.md:350–370

**Reasoning (Code vs Whitepaper)**

- Fault model and stake
  - `ByzantineStakeOK` encodes Assumption 1 exactly: `ByzantineStake * 100 < 20 * TotalStake` (strict inequality), matching “Byzantine nodes control less than 20% of the stake.” The stake primitives come from `Certificates.tla` (`StakeMap`, `TotalStake`, `CalculateStake`). This is also included as a safety invariant elsewhere, aligning theorems with the assumption’s scope.

- Partial synchrony timing
  - `AfterGST == time >= GST` is the expected latch for liveness arguments in §2.10. It is used by temporal properties later; defining it here is consistent with the model in §1.5 and the fairness notes in the spec.

- Rotor success threshold
  - `EnoughCorrectRelays(relays)` checks `|relays ∩ CorrectNodes| ≥ γ` with `γ = GammaDataShreds` from `Rotor.tla`, matching the threshold part of Definition 6. The full definition also requires a correct leader; the module later uses `RotorSuccessful(leader, relays, CorrectNodes)` to capture both parts precisely. This duplication is harmless but redundant (see Suggestions).

- Repair trigger
  - `NeedsBlockRepair(pool, block)` fires once Pool holds either a Notarization or Notar-Fallback certificate for the block. This matches §2.8: “After Pool obtains a certificate of signatures on Notar(slot(b), hash(b)) or NotarFallback(slot(b), hash(b)), the block b … needs to be retrieved.” It abstracts away the storage policy nuances described in §2.3 (e.g., storing only the finalized block for a slot) which are not critical to safety/liveness, but sufficient to trigger Algorithm 4.

- Initialization choices
  - Setting `validators[v]` with `InitValidatorState(v)` (from `VotorCore.tla`) establishes empty Pool, zeroed timers, and well-typed fields. Initializing `parentReady[1] = GenesisHash` and adding state `"ParentReady"` at slot 1 models the base case so the first leader window can proceed without waiting for a prior certificate on genesis. This is a standard modeling convention; it implicitly treats genesis as “ready” (cf. the ParentReady preconditions in Definition 15). Blocks start as `{GenesisBlock}` and each node’s `blockAvailability[v]` includes `GenesisBlock`, ensuring ancestry queries and leader-window logic have a well-defined base.

**Conclusion**

- The audited helpers and `Init` align with the whitepaper abstractions:
  - Assumption 1 is enforced via `ByzantineStakeOK`.
  - GST latch is represented by `AfterGST` for later liveness.
  - Rotor threshold is consistent with Definition 6; the precise form is provided by `RotorSuccessful` in `Rotor.tla`.
  - Repair trigger matches §2.8 (Definition 19, Algorithm 4) requirements.
  - Genesis bootstrapping (`ParentReady` for slot 1 with `GenesisHash`) is a reasonable abstraction to seed Algorithm 1 without introducing extraneous genesis certificates.

Overall, the code accurately reflects the intended whitepaper abstractions for these concerns and provides correct foundations for the subsequent actions and invariants in `MainProtocol`.

**Open Questions / Concerns**

- Redundant Rotor helper
  - `EnoughCorrectRelays` duplicates the threshold part of Definition 6 but omits the “leader is correct” condition. The module already uses `RotorSuccessful(leader, relays, CorrectNodes)` where needed. Keeping both can cause drift if definitions evolve.

- Explicit cardinality vs. declared `NumValidators`
  - This module introduces `NumValidators` but does not assert `Cardinality(Validators) = NumValidators`. The harness (`MC.cfg`) binds them consistently, but an assertion would prevent accidental divergence across models.

- Genesis ParentReady semantics
  - Initial `ParentReady` for slot 1 is a modeling assumption (reasonable), but it could be documented as “genesis is treated as certified/ready” to tie it back to Definition 15 more explicitly.

- Repair storage policy
  - The whitepaper’s storage policy (store only the finalized block for a slot, otherwise store blocks that may be needed before SafeToNotar) is simplified here to a trigger predicate. This is fine for the high-level model, but worth noting if storage policies become safety-relevant in future refinements.

**Suggestions for Improvement**

- Unify Rotor success helpers
  - Remove or deprecate `EnoughCorrectRelays` and use `Rotor.RotorSuccessful` uniformly. If you keep a local helper, redefine it to include the leader correctness: `leader \in CorrectNodes /\ Cardinality(relays \cap CorrectNodes) >= GammaDataShreds`.

- Tighten model–constant consistency
  - Add an assumption tying set size to the numeric parameter: `ASSUME Cardinality(Validators) = NumValidators`. This improves portability of the spec across model configs.

- Clarify genesis bootstrapping
  - Add a short comment near `Init` explicitly stating that genesis is considered “ParentReady” for slot 1 by fiat, as a base case consistent with Definition 15. This helps readers map the initialization to the event semantics.

- Optional: refine repair preconditions
  - If you later model storage capacity or bandwidth, extend `NeedsBlockRepair` to reflect the §2.3 storage policy (e.g., avoid repairing non-finalized alternatives once a block in the slot is finalized).

**Cross-File References (for this block)**

- Messages.tla: `Validators`, `Slots`, `BlockHashes`, `NoBlock` — `specs/tla/alpenglow/Messages.tla:12`
- Blocks.tla: `GenesisBlock`, `GenesisHash` — `specs/tla/alpenglow/Blocks.tla:22`
- VoteStorage.tla: `HasNotarizationCert`, `HasNotarFallbackCert` — `specs/tla/alpenglow/VoteStorage.tla:356`
- Certificates.tla: `TotalStake`, `CalculateStake` — `specs/tla/alpenglow/Certificates.tla:26`
- VotorCore.tla: `InitValidatorState`, `AddState` — `specs/tla/alpenglow/VotorCore.tla:41`
- Rotor.tla: `GammaDataShreds`, `RotorSuccessful` — `specs/tla/alpenglow/Rotor.tla:24`, `specs/tla/alpenglow/Rotor.tla:288`

