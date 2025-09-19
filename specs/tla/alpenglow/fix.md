Short answer: it’s close at a high level, but it’s **not fully correct/compliant with the Rotor spec in the whitepaper**, mainly because PS-P’s multi-bin assignments and per-bin sampling aren’t modeled. Here’s a quick review with fixes.

## What looks right

* **Erasure coding constants & resilience threshold.** You enforce `γ>0`, `Γ>0`, `γ<Γ`, and `3·Γ > 5·γ` (i.e., κ = Γ/γ > 5/3), matching Lemma 7’s over-provisioning requirement.&#x20;
* **Success predicate.** `RotorSuccessful` checks “leader is correct” and “≥ γ correct relays,” which is exactly Definition 6.&#x20;
* **Reconstruction threshold.** `SliceReconstructable(c) ≜ c ≥ γ` aligns with “any γ shreds suffice.”&#x20;
* **Next-leader latency hint.** Your `NextLeaderConstraint`/comment reflect the “send to next leader first” optimization.&#x20;

## The big gaps (and how to fix)

1. **PS-P Step 1 multiplicity is lost (sets can’t model it).**
   PS-P requires that a node with stake ρᵢ > 1/Γ occupy ⌊ρᵢ Γ⌋ **bins** (i.e., it may be picked multiple times for a single slice). Your `LargeStakeholders*` and `PSPConstraint` include each large stakeholder **at most once** because `sample` is a set. That deviates from Definition 46.&#x20;

**Fix:** Represent a selection **with multiplicity** as either:

* a **sequence** `Sel ∈ [1..Γ → Node]`, or
* a **function** `Bins ∈ [1..Γ → Node]` (one node per bin).

Then encode:

* Step 1: fill `floor(ρᵢ Γ)` distinct bin **indices** with node `i`.
* Step 2: partition remaining stakes across remaining bin indices.
* Step 3: sample **one** node per remaining bin proportional to stake.

You can always derive the set of relays as `RelaySet == {Bins[j] : j ∈ 1..Γ}` when you need set semantics elsewhere.

2. **No explicit partitioning & per-bin sampling.**
   `PSPSelect` uses a subset-choose (`CHOOSE S ∈ SUBSET ...`) and cardinalities. That abstracts away PS-P’s **binning** and **one-sample-per-bin** rule—the core variance-reduction idea in §3.1. Even a simple partitioner (“random order, cut after each 1/k stake”) is spelled out in the paper.&#x20;

**Fix:** Model a (possibly nondeterministic) **partitioning function**
`P(ρ', k) ∈ Partitionings` per Definition 45, then a **per-bin draw**.&#x20;

3. **Exact relay count vs. multiplicity.**
   `ExactRelayCountConstraint(sample)` requires `Cardinality(sample) = Γ`. If you switch to sequences/bins, `Cardinality({Bins[j]})` can be `< Γ` when a large stakeholder occupies multiple bins (duplicates collapse in a set). That’s fine—**the paper permits duplicates**—but your current invariant would reject valid PS-P outcomes.

**Fix:** Replace it with a constraint on the **number of bins**, e.g. `Len(Sel) = Γ`. When you need the broadcast set, use the set-projection as above.

4. **Stake-failure resilience is an extra assumption (fine, but name it).**
   `FailureResilient`/`ResilienceOK` introduce a stake floor after failures. The paper assumes <20% byzantine + up to 20% crashes in the liveness analysis; your parameters should either be tied to those numbers or clearly flagged as a **model extension**.&#x20;

**Fix:** Document that `RotorMaxFailedRelayStake` models the (crash+Byz) budget that the **chosen relays** might contain, and relate it to the global 40% headroom in the analysis, or parameterize it per your system goals.

## Smaller nits

* `MaxSlicesPerBlock` is declared but unused.
* `PSPSelectionPossible`’s reasoning about `totalSelected` equals “#largeStakeholders + remainingSlots” mirrors your simplified Step 1 (=1 per large stakeholder). Once you model **⌊ρᵢ Γ⌋** bins, update `deterministicCount` accordingly.&#x20;
* Consider an invariant like: if `RelaySet` is derived from bins, `RotorSuccessful(leader, RelaySet, correct)` is checked against **the set** while dissemination paths still use the **per-bin** mapping.

## Suggested TLA+ refactor sketch (conceptual)

* Replace `sample ⊆ needers` with:

  * `Bins ∈ [1..GammaTotalShreds → needers]`
  * `RelaySet == { Bins[j] : j ∈ 1..GammaTotalShreds }`
* Encode PS-P:

  * `DetBins(i) == ⌊(StakeMap[i]/TotalStake)*GammaTotalShreds⌋`
  * Pre-fill that many bin indices with `i`.
  * For remaining bins, use a partitioning value `P` (Definition 45) and sample 1 node per bin proportional to stake.
* Keep `NextLeaderConstraint` by requiring `∃j: Bins[j] = nextLeader` when `nextLeader ∈ needers`.&#x20;
* Define `ExactRelayBins == DOMAIN Bins = 1..GammaTotalShreds` (not set cardinality).

---

### Verdict

* **Conceptually aligned** on γ/Γ, success condition, and the next-leader optimization.
* **Not yet correct** with respect to PS-P **as defined**: you need bin-level multiplicity and per-bin sampling to match Definition 46 and the variance-reduction guarantees. Once you represent selections as a length-Γ sequence/function over bins and implement Steps 1–3 literally, you’ll be whitepaper-compliant.&#x20;

If you want, I can turn the above into concrete TLA+ operators (`PartitionOK`, `FillLarge`, `SampleFromBins`, `BinsToRelaySet`) so you can drop them into your module.
