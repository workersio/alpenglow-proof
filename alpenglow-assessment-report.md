**Alpenglow TLA+ Assessment Report**

- Scope: Formal alignment of the TLA+ specification under `specs/tla/alpenglow` with the whitepaper claims and definitions in `alpenglow-whitepaper.md`.
- Method: Cross-checked each modeled subsystem (Rotor, Blokstor, Votor, Pool) and each required property class (safety, liveness, resilience) against the whitepaper. File and line references point to the exact definitions relied upon.

**Methodology**
- Read whitepaper sections for Rotor (§2.2), Blokstor (§2.3), Votes/Certificates/Pool (§2.4–§2.5), Votor (§2.6–§2.8), Safety (§2.9), Liveness (§2.10), Smart Sampling (§3.1) and top-level assumptions (§1.5).
- Traced the TLA+ modules for corresponding structure, actions, and predicates:
  - Messages: specs/tla/alpenglow/Messages.tla
  - Blocks/Windows: specs/tla/alpenglow/Blocks.tla
  - Certificates: specs/tla/alpenglow/Certificates.tla
  - Pool/Vote storage and aggregation: specs/tla/alpenglow/VoteStorage.tla
  - Votor state machine and timeouts: specs/tla/alpenglow/VotorCore.tla
  - Rotor dissemination and sampling: specs/tla/alpenglow/Rotor.tla
  - Protocol tie-in, invariants, temporal properties: specs/tla/alpenglow/MainProtocol.tla and model harness specs/tla/alpenglow/MC.cfg

**Coverage Assessment**

- Votor dual voting paths (fast 80% vs slow 60%)
  - Whitepaper: Tables 5–6 and §2.6 fast/slow timing (alpenglow-whitepaper.md:476–507, 600).
  - Spec: Certificate thresholds 80%/60% (specs/tla/alpenglow/Certificates.tla:47–49, 284–296). Slow/fast finalization application (specs/tla/alpenglow/MainProtocol.tla:241–259). TRYNOTAR/TRYFINAL mapping (specs/tla/alpenglow/VotorCore.tla:191–215, 164–177).
  - Pool enforces “count once per slot” and uniqueness (specs/tla/alpenglow/VoteStorage.tla:446–455, 478–486) per Definition 12–13 (alpenglow-whitepaper.md:513–520, 532–534).

- Rotor erasure-coded propagation with stake-weighted relay sampling
  - Whitepaper: Definition 6 and Lemmas 7–9 (alpenglow-whitepaper.md:414–439); Smart Sampling PS-P (§3.1, Definition 46 at alpenglow-whitepaper.md:1154–1160).
  - Spec: Γ/γ parameters and κ>5/3 (specs/tla/alpenglow/Rotor.tla:46–63). PS‑P bin structure and constraints (specs/tla/alpenglow/Rotor.tla:157–166, 181–186, 197–206). Success predicates by bins (specs/tla/alpenglow/Rotor.tla:232–240). Protocol use in delivery actions (specs/tla/alpenglow/MainProtocol.tla:674–679).

- Certificate generation, aggregation, uniqueness
  - Whitepaper: Definition 13, Table 6 (alpenglow-whitepaper.md:520–524, 532, 499–507).
  - Spec: GenerateCertificate discovers and prioritizes candidates (specs/tla/alpenglow/VoteStorage.tla:245–310), uniqueness at store-time (specs/tla/alpenglow/VoteStorage.tla:473–486), valid/formed certificate checks (specs/tla/alpenglow/Certificates.tla:269–296, 302–316), and “fast ⇒ notar” inclusion (specs/tla/alpenglow/Certificates.tla:330–337) reflected at pool level (specs/tla/alpenglow/MainProtocol.tla:935–946).

- Timeout mechanisms and skip certificate logic
  - Whitepaper: Definition 17 timeout formula (alpenglow-whitepaper.md:607–613); fallback Definitions 16 (alpenglow-whitepaper.md:554–573).
  - Spec: SETTIMEOUTS matches formula with Δ_timeout and Δ_block (specs/tla/alpenglow/VotorCore.tla:325–341). SafeToNotar / SafeToSkip guards mirror thresholds precisely (specs/tla/alpenglow/VoteStorage.tla:321–339, 347–356). Emission and handlers wired into event loop (specs/tla/alpenglow/MainProtocol.tla:593–603, 615–628; specs/tla/alpenglow/VotorCore.tla:208–215, 362–389).

- Leader rotation and window management
  - Whitepaper: Windows and public schedule (§1.1/§2.7, alpenglow-whitepaper.md:53, 222, 678).
  - Spec: WindowIndex/Leader/WindowSlots (specs/tla/alpenglow/Blocks.tla:208–225, 243–248) and ParentReady gating at first slot (specs/tla/alpenglow/MainProtocol.tla:642–652; specs/tla/alpenglow/VotorCore.tla:191–203, 320–341).

**Machine-Verified Theorems**

- Safety
  - No conflicting finalization same slot: invariant present (specs/tla/alpenglow/MainProtocol.tla:744–747). Whitepaper Theorem 1 (alpenglow-whitepaper.md:930).
  - Single-chain consistency: SafetyInvariant plus ancestor-closure (specs/tla/alpenglow/MainProtocol.tla:732–736; specs/tla/alpenglow/Blocks.tla:294–299; 181–185). Assumption 1 bounds are encoded (alpenglow-whitepaper.md:107; specs/tla/alpenglow/MainProtocol.tla:120–131, 1326–1331 via ByzantineStakeOK in Invariant).
  - Certificate uniqueness and non-equivocation: local uniqueness and type-wise non‑equivocation (specs/tla/alpenglow/VoteStorage.tla:478–486; specs/tla/alpenglow/MainProtocol.tla:834–847). Pool/Transit well-formedness checks (specs/tla/alpenglow/MainProtocol.tla:900–916, 920–927, 950–963).

- Liveness
  - Whitepaper theorem 2 window liveness (alpenglow-whitepaper.md:1045) is modeled as temporal property WindowFinalizationAll (specs/tla/alpenglow/MainProtocol.tla:1124–1131) with explicit “no pre‑GST timeouts” premise (1105–1109).
  - Generic progress after GST: BasicLiveness and Progress (specs/tla/alpenglow/MainProtocol.tla:1057–1062, 1090–1096) match §1.5 partial synchrony (alpenglow-whitepaper.md:228–241) at a high level.

- Resilience
  - Safety with ≤20% Byzantine stake: Assumption 1 restated and enforced (alpenglow-whitepaper.md:107; specs/tla/alpenglow/MainProtocol.tla:1326–1331 in Invariant, and the model harness constrains ByzantineCount/StakeMap in specs/tla/alpenglow/MC.tla:9–23).
  - Rotor success/failure and repair actions are present (alpenglow-whitepaper.md:414–470; specs/tla/alpenglow/MainProtocol.tla:658–679, 480–490), but liveness under crash/non‑responsive fractions is not separately parameterized in the model (see Critical Gaps).

**Critical Gaps and Drifts**

1) Missing temporal property for fast‑path one‑round finalization (>80% responsive stake)
- Whitepaper claim and thresholds: Tables 6 + §2.6 state blocks finalize in one round with ≥80% participating stake (alpenglow-whitepaper.md:499–507, 600).
- Spec status: Thresholds and fast certificate validity exist (specs/tla/alpenglow/Certificates.tla:47–49, 284–287) and finalization action consumes FastFinalizationCert (specs/tla/alpenglow/MainProtocol.tla:241–259). However, there is no temporal property that asserts “if ≥80% NotarVote for b in slot s, then b fast‑finalizes in one round” under post‑GST delivery/fairness.
- Why this is necessary: The primary task requires machine‑verified theorems including “Fast path completion in one round with >80% responsive stake.” Without an explicit temporal property tied to the fast cert preconditions, model checking cannot confirm this claim.

2) Missing bounded‑time finalization property min(δ80%, 2δ60%)
- Whitepaper claim: Section 1.3 and §2.6 assert bounded latency min(δ80%, 2δ60%) (alpenglow-whitepaper.md:126, 600; δθ defined at 241).
- Spec status: Timeouts model Δ_timeout and Δ_block (specs/tla/alpenglow/VotorCore.tla:325–341) and Rotor models a qualitative next‑leader latency hint (specs/tla/alpenglow/Rotor.tla:236–240), but δ80% and δ60% are not parameterized and no temporal bound links voting thresholds to finalization time.
- Why this is necessary: The task explicitly asks to verify the bounded finalization time claim. Absent δ80%/δ60% parameters and a property bounding the temporal distance from block delivery to finalization, TLC cannot check this bound.

3) Missing explicit liveness guarantee under >60% honest participation
- Whitepaper basis: With >60% honest participation (and ≤20% Byzantine; possibly ≤20% additional crashed under Assumption 2), two‑round path guarantees progress (alpenglow-whitepaper.md:122–124, 600; §2.10 Lemmas 35–40 at 953–1016).
- Spec status: Generic liveness (BasicLiveness/Progress) and window‑liveness (WindowFinalizationAll) exist (specs/tla/alpenglow/MainProtocol.tla:1057–1062, 1090–1096, 1124–1131). None of these properties are conditioned on a modeled “≥60% responsive” predicate or constant; the model doesn’t parameterize “non‑responsive stake” separate from Byzantine.
- Why this is necessary: The task requires “Progress guarantee under partial synchrony with >60% honest participation.” Without a model parameter for non‑responsive stake or a property that quantifies progress contingent on “≥60% responsive,” TLC cannot verify this claim as stated.

4) Missing resilience property for liveness with ≤20% non‑responsive stake (crash tolerance)
- Whitepaper Assumption 2 (alpenglow-whitepaper.md:122) distinguishes Byzantine (<20%) and additional crashed (≤20%) stake.
- Spec status: There is no separate “crashed/non‑responsive” set; only `byzantineNodes` exist (specs/tla/alpenglow/MainProtocol.tla:103–114). Fairness is applied to actions of correct nodes post‑GST, but the model does not encode “some correct nodes are unresponsive” nor a property guaranteeing progress in that case.
- Why this is necessary: The task requires “Liveness maintained with ≤20% non responsive stake.” This needs a parameterization and a liveness property quantifying over that condition to be model‑checked.

5) Missing explicit network partition recovery property
- Whitepaper: Partial synchrony via GST (alpenglow-whitepaper.md:228–241) implies recovery of liveness after arbitrary asynchrony.
- Spec status: Fairness gates actions by `AfterGST` (specs/tla/alpenglow/MainProtocol.tla:696–714), and generic liveness (BasicLiveness) asserts eventual finalization after GST (1057–1062). However, there is no explicit “recovery” property that states: “from any pre‑GST history, once time ≥ GST, progress resumes.”
- Why this matters: The task requires “Network partition recovery guarantees.” A succinct temporal property that ties pre‑GST asynchrony to post‑GST progress would let TLC check this claim directly.

6) Minor, but correctness‑critical alignment: Window‑level premises
- Whitepaper: No timeouts before GST (alpenglow-whitepaper.md:613), leader correctness, and repair prerequisites drive §2.10 proofs.
- Spec status: WindowFinalization(s) includes “Leader(s) ∈ CorrectNodes” and NoTimeoutsBeforeGST(s) (specs/tla/alpenglow/MainProtocol.tla:1124–1131), which is consistent. Nothing to change here; included for completeness because the liveness properties in PROPERTIES currently rely on this premise and not on >60% responsiveness.

**What Works As‑Is (Confirmed)**
- Data model and windows (Blocks) match §2.1/§2.7 including window helpers and schedule adherence (specs/tla/alpenglow/Blocks.tla:208–229, 243–248).
- Vote and certificate types and well‑formedness follow Table 5/6 (specs/tla/alpenglow/Messages.tla:87–129, 180–213).
- Pool multiplicity and uniqueness follow Definition 12/13 (specs/tla/alpenglow/VoteStorage.tla:446–455, 473–486) and “fast ⇒ notar” (specs/tla/alpenglow/Certificates.tla:330–337).
- SafeToNotar and SafeToSkip exactly encode Definition 16 (specs/tla/alpenglow/VoteStorage.tla:321–339, 347–356; whitepaper alpenglow-whitepaper.md:565–573).
- Finalization action matches Definition 14 (specs/tla/alpenglow/MainProtocol.tla:241–259; whitepaper alpenglow-whitepaper.md:536–541).
- Rotor success and PS‑P modeling align with Definition 6 and §3.1 (specs/tla/alpenglow/Rotor.tla:157–166, 232–240; whitepaper alpenglow-whitepaper.md:414, 1154–1160).
- Safety invariants encode Theorem 1 and corollaries (specs/tla/alpenglow/MainProtocol.tla:732–747, 779–792; whitepaper alpenglow-whitepaper.md:930).

**Recommendations To Close Critical Gaps**
- Add temporal “FastPathOneRound” property: After GST, if a slot attains a FastFinalizationCert (or equivalently ≥80% NotarVote per Table 6) then the block is eventually finalized in one round. This should be expressed as a PROPERTIES item in `MC.cfg`, driven by predicates already present (e.g., certificate presence and FinalizeBlock action).
- Encode δ80% and δ60% (or abstract bounds) and assert a bounded‑time finalization relation from Block delivery to finalization consistent with min(δ80%, 2δ60%). Without these parameters, TLC cannot check the claimed bound.
- Parameterize “non‑responsive” stake (distinct from Byzantine) and add a liveness property asserting progress with ≤20% non‑responsive stake and ≤20% Byzantine (Assumption 2), matching whitepaper §1.5/§2.10.
- Add an explicit “post‑GST recovery” temporal property that from any pre‑GST state, liveness resumes after GST. This can reuse BasicLiveness but should be stated to quantify over arbitrary histories.

Each recommendation directly targets a missing verification artifact required by the task. No changes to low‑level mechanics are proposed.

**References (selected)**
- Whitepaper
  - Rotor Definition 6, Lemmas 7–9: alpenglow-whitepaper.md:414–439
  - Blokstor event: alpenglow-whitepaper.md:468–470
  - Votes/Certificates (Tables 5–6): alpenglow-whitepaper.md:489–507
  - Pool Def. 12–16: alpenglow-whitepaper.md:513–573
  - Finalization Def. 14: alpenglow-whitepaper.md:536–541
  - Timeouts Def. 17: alpenglow-whitepaper.md:607–613
  - Votor Algs. 1–2: alpenglow-whitepaper.md:634–666, 676–711
  - Block creation Alg. 3: alpenglow-whitepaper.md:759–776
  - Repair Alg. 4: alpenglow-whitepaper.md:801–814
  - Safety Theorem 1: alpenglow-whitepaper.md:930
  - Liveness Theorem 2: alpenglow-whitepaper.md:1045
  - Assumptions / partial synchrony: alpenglow-whitepaper.md:100–108, 226–241

- Spec
  - Certificates thresholds/validity: specs/tla/alpenglow/Certificates.tla:47–49, 269–296
  - Pool multiplicity/uniqueness: specs/tla/alpenglow/VoteStorage.tla:446–455, 473–486
  - SafeToNotar/Skip: specs/tla/alpenglow/VoteStorage.tla:321–339, 347–356
  - Finalization action: specs/tla/alpenglow/MainProtocol.tla:241–259
  - Safety invariants: specs/tla/alpenglow/MainProtocol.tla:732–747
  - Window liveness: specs/tla/alpenglow/MainProtocol.tla:1124–1131
  - Rotor PS‑P and success: specs/tla/alpenglow/Rotor.tla:157–166, 232–240

