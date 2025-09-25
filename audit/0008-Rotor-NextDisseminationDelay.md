## 1. Code Under Audit

```tla
NextDisseminationDelay(sample, nextLeader) == IF nextLeader \in sample THEN 0 ELSE 1
```

## 2. Whitepaper Sections and References

- Latency bounds
  - `alpenglow-whitepaper.md:429`: Latency section — Rotor latency between δ and 2δ.
  - `alpenglow-whitepaper.md:431`: Lemma 8 — If Rotor succeeds, latency ≤ 2δ; high κ can reduce latency toward δ.
  - `alpenglow-whitepaper.md:433`: Proof sketch — 2-hop δ + δ model.

- Fast leader handoff motivation
  - `alpenglow-whitepaper.md:170`: “Fast leader handoff” — next leader can start producing once it has the previous block.

- Definition location in spec
  - `specs/tla/alpenglow/Rotor.tla:224`: Function defined with an explanatory comment as a “latency hint.”

## 3. Reasoning and Whitepaper Alignment

- Abstraction intent
  - The function provides a coarse latency hint for the next leader’s receipt relative to the relay sample: if the next leader is among selected relays, it incurs no additional delay (0), otherwise an extra unit (1). This aligns with the two-hop δ vs. (δ+δ) intuition from Lemma 8.

- Interaction with constraints
  - `Rotor.tla` also includes `NextLeaderConstraint(bins, needers, nextLeader)` to bias relay assignment toward including the next leader when it still needs the block. Together, the constraint and this function express “send to next leader first” as both a structural preference and a latency accounting hint.

- Scope and usage
  - The function is not (yet) consumed elsewhere in the model; it is explicitly labeled advisory. It can inform time progression or scheduling choices to model faster handoff when the next leader is included.

## 4. Audit Conclusion

- The function matches the whitepaper’s latency narrative: including the next leader among relays brings observed latency closer to δ for leader handoff; otherwise, it is closer to 2δ.
- Keeping it advisory is consistent with focusing on abstraction over implementation detail and avoids prematurely committing to a specific time model.

## 5. Open Questions or Concerns

- Path assumption: Membership alone (`nextLeader \in sample`) does not capture whether the next leader is “on-path” (geographically favorable) as hinted in the Lemma 8 proof sketch. The model treats this as an abstract 0/1 hint, which is acceptable, but worth documenting.
- Unused at present: Since no action consumes the value, any intended impact on time or scheduling is currently implicit. If handoff speed affects safety/liveness elsewhere, consider wiring it in.

## 6. Suggestions for Improvement

- Connect to time progression: Use `NextDisseminationDelay` in the steps that advance time or trigger the next leader’s proposal, to explicitly reflect fast handoff when applicable.
- Naming clarity: Consider renaming parameter `sample` to `relays` for alignment with the rest of Rotor (or document that `sample` is “the set of selected relays”).
- Optional refinement: Introduce an abstract predicate (e.g., `OnPath(nextLeader, relays)`) to separate “membership” from “on-path routing” if modeling nuance around δ vs. 2δ becomes important, while keeping it abstract and non-implementation specific.

