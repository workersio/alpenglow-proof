
# Alpenglow Liveness — Lemmas (Definitions) and Final Theorem

This file lists the **lemmas required from the whitepaper** and gives their **precise definitions (statements)** in a spec-friendly form so they can be referenced from TLAPS. At the end we state the **Final Liveness Theorem** that combines the three properties you asked to prove.

---

## Notation & Predicates (used in statements)
- `StakeOf(S)`: total stake of validator set `S`. `TotalStake` is the total stake.
- Thresholds: `DefaultThreshold = 60% * TotalStake`, `FastFinalThreshold = 80% * TotalStake`.
- `Honest`: set of honest validators. `Responsive ⊆ Honest` are post-GST responsive.
- `Avail60Now(s,h)`, `Avail80Now(s,h)`: at the current time, at least 60% / 80% stake has the proposal `(slot s, hash h)` available.
- `HasNotarizationCert(s,h)`, `HasFastFinalizationCert(s,h)`, `HasNotarFallbackCert(s)`, `HasSkipCert(s)`: corresponding certificates exist system-wide for the indicated slot/hash.
- `EmitNotarVote(s,h)`, `EmitSkipVote(s)`: a validator’s vote actions.
- `Timeout(s)`: per-slot timeout is set for all correct validators.
- `ParentReady(W)`: a window `W` of slots is active and ready (timeouts should be set).
- `FinalizedAt(s,h)`: block `(s,h)` is finalized (enters the finalized set).
- Time constants: `δ60` (delivery bound to ≥60% stake), `δ80` (delivery bound to ≥80% stake). In code these correspond to `Delta60`, `Delta80`.

---

## Transport & Availability

### Lemma 7 — Rotor Resilience
**Definition.** If the leader is honest and the required fraction of relay nodes are honest, then the rotor broadcast succeeds with high probability (w.h.p.), i.e., the leader’s proposal is disseminated across the overlay without adversarial suppression.

### Lemma 8 — Rotor Latency (δ-Quantiles)
**Definition.** After GST and conditioned on rotor success, any message broadcast at time `t` reaches a set of validators with stake ≥`q` by time `t + δ_q`, for `q ∈ {60%, 80%}`. (These bounds map to `δ60`, `δ80`.)

---

## Vote Discipline, Uniqueness, Fast Semantics

### Lemma 20 — Exactly-One Vote Per Slot (Notarization **or** Skip)
**Definition.** Every honest validator casts **exactly one** vote in each slot `s`, which is either a notarization vote for some block `(s,h)` or a skip vote for `s`, but not both.

### Lemma 21 — Fast-Finalization Dominance
**Definition.** If a fast-finalization certificate exists for `(s,h)`, then simultaneously:  
(i) no other block at slot `s` can be notarized;  
(ii) no notar-fallback certificate for `s` can exist;  
(iii) no skip certificate for `s` can exist.

### Lemma 23 — Unique Notarization from >40% Aligned Honest Notar Votes
**Definition.** If >40% honest stake notarizes the same block `(s,h)`, then no other block in slot `s` can be notarized.

### Lemma 24 — At-Most-One Notarized Block Per Slot
**Definition.** For every slot `s`, there is at most one notarized block.

### Lemma 25 — Finalization Implies Notarization Support
**Definition.** If `(s,h)` is finalized (fast or slow path), then there exists either a fast-finalization certificate for `(s,h)` or a notarization certificate for `(s,h)` (i.e., finalization never occurs without notar support).

### Lemma 26 — Slow-Finalization Ancestry
**Definition.** If `(s,h)` is finalized via the slow path, then the parent at slot `s−1` is either notarized or has a notar-fallback certificate consistent with `(s,h)`’s chain, ensuring ancestry compatibility.

---

## Certificate Causality (Votes ↔ Certificates)

### Lemma 27 — Certificate ⇒ Some Honest Notar Vote
**Definition.** If a notarization or notar-fallback certificate exists for `(s,h)`, then at least one honest validator must have cast a notarization vote for `(s,h)`.

### Lemma 28 — Honest Notar Vote ⇒ Final Vote for Parent
**Definition.** If an honest validator cast a notarization vote for `(s,h)`, then it subsequently casts a finalization (or fallback) vote that supports the parent in slot `s−1`.

### Lemma 29 — Notar-Fallback Vote ⇒ >40% Honest Notar Support for Parent
**Definition.** If an honest validator cast a notar-fallback vote for `(s,h)`, then >40% honest stake cast notarization votes for the parent at slot `s−1`.

### Lemma 30 — Notar at s ⇒ Prior Support at s−1
**Definition.** If `(s,h)` is notarized in slot `s`, then in slot `s−1` either the parent was notarized or there existed a notar-fallback for the parent.

---

## Timeout Orchestration / Window Progress

### Lemma 33 — ParentReady ⇒ Timeouts Scheduled for Window
**Definition.** If `ParentReady(W)` holds for a window of slots `W`, then each honest validator schedules `Timeout(s)` for every slot `s ∈ W`.

### Lemma 34 — Timeout Monotonicity (Within a Window)
**Definition.** If `Timeout(s)` is scheduled by all honest validators for some `s` in window `W`, then for every earlier slot `s' < s` in `W`, `Timeout(s')` is also scheduled by all honest validators.

### Lemma 35 — All Timeouts Set ⇒ Everyone Votes (Notar or Skip)
**Definition.** If all honest validators have `Timeout(s)` set, then each honest validator will cast either a notarization vote for some `(s,h)` or a skip vote for `s` (exactly one, by Lemma 20).

### Lemma 36 — No >40% Notar Signal ⇒ No Premature 'ItsOver'
**Definition.** If in slot `s` no set of notar votes exceeds 40% honest stake, then no honest validator sets the terminal flag for `s` (i.e., no premature completion).

### Lemma 37 — All Timeouts Set ⇒ >40% Aligned Notar in s
**Definition.** If all honest validators set `Timeout(s)`, then >40% honest stake will notarize the **same** block in slot `s` (provided rotor dissemination succeeds).

### Lemma 38 — >40% Aligned Notar ⇒ Notar-Fallback Cert (if no full notar yet)
**Definition.** If >40% honest stake notarizes the same block `(s,h)` but the full notar threshold isn’t yet met, a notar-fallback certificate for `(s,h)` will be produced/observed; otherwise a notarization certificate will be produced directly.

### Lemma 39 — Rotor + Timeouts ⇒ Every Slot Gets a Cert
**Definition.** If all honest validators set timeouts for a window and rotor succeeds for that window, then **every slot** in the window obtains either a notarization certificate for some `(s,h)` or a skip certificate.

### Lemma 40 — Window Completion ⇒ Next Window Becomes ParentReady
**Definition.** Once a node observes decisive certificates for all slots in the current window, it marks `ParentReady` for the next window.

### Lemma 41 — Eventually, All Windows’ Timeouts are Set
**Definition.** After GST, by iterating Lemmas 39 and 40, all windows repeatedly become `ParentReady` and all timeouts are set by all honest validators.

### Lemma 42 — From First Notar at t ⇒ Timeouts Everywhere by t + Δ
**Definition.** After GST, if the first notarization in the active window is observed at time `t`, then by `t + Δ` all honest validators have set timeouts for that window.

---

## Auxiliary Arithmetic / Set Lemmas (used implicitly)
- **Monotonicity of thresholds.** If `stake ≥ 80%` then `stake ≥ 60%`.
- **Quorum intersection.** For stake thresholds `q1, q2`, any two sets exceeding them intersect with stake at least `(q1+q2−1)*TotalStake`.
- **Count-once property.** In certificate aggregation, each validator’s stake is counted at most once.

---

## Final Liveness Theorem (Combined Statement)

**Theorem (Main Liveness, Partial Synchrony).** Assume GST holds, the adversary’s Byzantine stake is within bounds, and the leader schedule is fair. Then:

1. (**Progress under ≥60% honest participation**)  
   Eventually, some block is finalized by all honest validators.

2. (**Fast path in one round under ≥80% responsive stake**)  
   If at some time `t` after GST, `Avail80Now(s,h)` holds, then a fast-finalization certificate for `(s,h)` is produced and `(s,h)` is finalized **within** `δ80` (i.e., inside the same round).

3. (**Bounded finalization time**)  
   For any `(s,h)` that becomes available to the network after GST, the time to finalization is bounded by  
   \[ \, 	ext{FinalizationTime}(s,h) \le \min \{ \delta_{80},\; 2\,\delta_{60} \} \, . \]

These three conclusions follow by composing the lemmas listed above as follows: (i) Lemmas 7–8, 33–42, 20, 23–26, 27–30 give slow-path progress and finalization; (ii) Lemmas 7–8 and 21 give the fast-path finalization; (iii) the bounds use the δ-quantiles from Lemma 8 and the two-step slow-path bound (two applications of `δ60`).

---

*End of file.*
