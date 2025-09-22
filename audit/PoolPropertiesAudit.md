# Audit Report: Pool Invariants

This report audits the TLA+ invariants `PoolMultiplicityOK` and `PoolCertificateUniqueness` against the Alpenglow whitepaper.

## 1. Code Under Audit

The following TLA+ code defines two system-wide invariants that apply to the `pool` data structure of each validator.

```tla
PoolMultiplicityOK ==
    \A v \in Validators : MultiplicityRulesRespected(validators[v].pool)

PoolCertificateUniqueness ==
    \A v \in Validators : CertificateUniqueness(validators[v].pool)
```

These operators are defined in `specs/tla/alpenglow/MainProtocol.tla` and are checked as part of the main state invariant, ensuring these properties hold true in every reachable state of the model. They rely on helper operators defined in `specs/tla/alpenglow/VoteStorage.tla`.

## 2. Whitepaper References

The audited code corresponds to rules laid out in Section 2.5 "Pool" of the whitepaper.

**Reference for `PoolMultiplicityOK`:**

> **Definition 12 (storing votes)** - (Page 20)
> *Pool stores received votes for every slot and every node as follows:*
> * *The first received notarization or skip vote,*
> * *up to 3 received notar-fallback votes,*
> * *the first received skip-fallback vote, and*
> * *the first received finalization vote.***

**Reference for `PoolCertificateUniqueness`:**

> **Definition 13 (certificates)** - (Page 21)
> *A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool.***

## 3. Reasoning and Analysis

### 3.1. `PoolMultiplicityOK`

The `PoolMultiplicityOK` invariant iterates through every validator (`\A v \in Validators`) and applies the `MultiplicityRulesRespected` check to its local pool.

The `MultiplicityRulesRespected` operator, defined in `VoteStorage.tla`, is a direct formalization of the rules from Definition 12:

```tla
MultiplicityRulesRespected(pool) ==
    \A s \in Slots, v \in Validators :
        LET votes == pool.votes[s][v]
        IN /\ Cardinality({vt \in votes : vt.type = "NotarVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "SkipVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "NotarFallbackVote"}) <= 3
           /\ Cardinality({vt \in votes : vt.type = "SkipFallbackVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "FinalVote"}) <= 1
```

- The whitepaper's "first received notarization or skip vote" directly translates to a cardinality of `<= 1`.
- "up to 3 received notar-fallback votes" translates to `<= 3`.
- "first received skip-fallback vote" translates to `<= 1`.
- "first received finalization vote" translates to `<= 1`.

The TLA+ code correctly and precisely models the vote storage multiplicity rules from the whitepaper.

### 3.2. `PoolCertificateUniqueness`

The `PoolCertificateUniqueness` invariant iterates through every validator and applies the `CertificateUniqueness` check to its pool. This check formalizes the rule from Definition 13.

The `CertificateUniqueness` operator is defined in `VoteStorage.tla`:

```tla
CertificateUniqueness(pool) ==
    \A s \in Slots :
        \A c1, c2 \in pool.certificates[s] :
            (c1.type = c2.type /\ c1.slot = c2.slot) =>
            (c1.type \in {"SkipCert", "FinalizationCert"} \/ c1.blockHash = c2.blockHash)
```

This logic states that for any given slot `s`, if two certificates (`c1`, `c2`) in the pool have the same type:
1.  If the type is `SkipCert` or `FinalizationCert`, this implies `c1` and `c2` must be the same certificate, enforcing uniqueness. The formula allows this case (`c1.type \in {"SkipCert", "FinalizationCert"}`). If they were different certificates of the same type, the implication would be false, violating the invariant.
2.  If the type is a notarization-related type (e.g., `NotarizationCert`), they must also share the same `blockHash`. This is a crucial safety detail: it prevents a validator's pool from containing two notarization certificates for the *same slot* but for *different blocks*.

This is a correct and more precise formalization of the whitepaper's statement "A single... certificate of each type... is stored". The TLA+ clarifies the implicit requirement that you cannot notarize two different blocks in the same slot.

## 4. Conclusion

The TLA+ invariants `PoolMultiplicityOK` and `PoolCertificateUniqueness` are **correct** and **faithful** formalizations of the rules specified in **Definition 12** and **Definition 13** of the Alpenglow whitepaper. The code accurately captures the specified constraints on vote multiplicity and certificate uniqueness within each validator's pool.

## 5. Open Questions or Concerns

- None. The mapping between the specification and the whitepaper is direct and clear.

## 6. Suggestions for Improvement

- The comments in `VoteStorage.tla` are excellent and already link to the relevant definitions. For even quicker reference, adding the page number (e.g., "Definition 12 (page 20)") could be a minor enhancement.
