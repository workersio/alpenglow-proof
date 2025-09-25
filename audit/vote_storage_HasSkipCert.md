# Audit: VoteStorage.HasSkipCert(pool, slot)

## 1. Code Under Audit

```tla
HasSkipCert(pool, slot) ==
    \E cert \in pool.certificates[slot] :
        cert.type = "SkipCert"
```

Location: `specs/tla/alpenglow/VoteStorage.tla:233`

## 2. Whitepaper Sections and References

- Certificates generation/storage (Definition 13): `alpenglow-whitepaper.md:520`
- ParentReady requires skip certs for all gap slots (Definition 15): `alpenglow-whitepaper.md:546`
- Fallback events, SafeToSkip definition (Definition 16): `alpenglow-whitepaper.md:571`
- Certificates overview and the role of skip certificates (§2.4): `alpenglow-whitepaper.md:476`, `alpenglow-whitepaper.md:507`
- Fast/slow path imply no skip cert can coexist with notarized slot (Lemmas 21, 26): `alpenglow-whitepaper.md:830`, `alpenglow-whitepaper.md:878`

Related spec anchors for context:
- Certificate type includes `"SkipCert"`: `specs/tla/alpenglow/Messages.tla:146`
- Skip certificate creation/guard: `specs/tla/alpenglow/Certificates.tla:177`, `specs/tla/alpenglow/Certificates.tla:243`
- Pool certificate storage rules and uniqueness: `specs/tla/alpenglow/VoteStorage.tla:115`
- Skip vs block-certificate mutual exclusion property: `specs/tla/alpenglow/Certificates.tla:433`
- Uses of `HasSkipCert` in protocol:
  - ParentReady gap check: `specs/tla/alpenglow/VoteStorage.tla:272`
  - Suppress redundant SafeToSkip fallback casting: `specs/tla/alpenglow/MainProtocol.tla:655`

## 3. Reasoning vs. Whitepaper Claims

- Purpose and abstraction.
  - The whitepaper models skip as a slot-scoped outcome with a dedicated certificate type (Table 6). ParentReady requires that all slots between a prior certified block and the start of a new leader window be covered by skip certificates (Def. 15, ParentReady).
  - The operator under audit abstracts this as a simple existential query over the pool’s certificate set for slot `s`.

- Pool typing and storage discipline.
  - The pool stores certificates keyed by slot: `pool.certificates: [Slots -> SUBSET Certificate]` (VoteStorage). Certificates themselves carry a `type` and a `slot` (Messages). Store paths enforce validity and per-type uniqueness per slot (VoteStorage.CanStoreCertificate; Certificates.SkipVsBlockCertExclusion).
  - Therefore, checking existence of any certificate with `type = "SkipCert"` inside `pool.certificates[slot]` is sufficient to conclude “a skip certificate for this slot is present.” No block hash match is required because skip certificates are slot-only (`blockHash = NoBlock`).

- Alignment with ParentReady (Def. 15).
  - The spec uses `\A s ∈ (parentSlot+1)..(slot−1) : HasSkipCert(pool, s)` to encode the requirement that every gap between the certified parent and the window’s first slot has a skip certificate. This exactly mirrors the text of Definition 15.

- Compatibility with fallback event logic (Def. 16).
  - The model suppresses emitting SafeToSkip if a skip certificate already exists using `~HasSkipCert(pool, s)` (MainProtocol), which is consistent: once the skip outcome is certified, further skip-fallback voting is redundant.

- Safety and exclusivity.
  - The whitepaper’s Lemmas 21 and 26 state that if a slot is fast/slow finalized (via block certificates), a skip certificate cannot exist for the same slot. The spec reinforces this via the invariant `SkipVsBlockCertExclusion`, and `GenerateCertificate` gates skip creation when any block certificate is creatable. `HasSkipCert` does not itself enforce this but is safe in the presence of these invariants.

## 4. Conclusion

`HasSkipCert(pool, slot)` faithfully captures the intended abstraction “slot s has a skip certificate in the local Pool,” which is exactly what is needed for:
- ParentReady’s gap coverage check (Def. 15), and
- Avoiding redundant emission of skip-fallback voting logic once skipping is certified (Def. 16).

Given the surrounding storage rules (single certificate per type/slot, skip-vs-block exclusion) and certificate validity checks on store and delivery, the existential test over `pool.certificates[slot]` by `type = "SkipCert"` is correct and sufficient relative to the whitepaper.

## 5. Open Questions or Concerns

- Cross-node timing: ParentReady and SafeToSkip depend on locally known certificates. This is inherent to the model, but operationally, late delivery could delay ParentReady despite sufficient global stake. The specification is consistent with the whitepaper, which also reasons in terms of local Pool contents.
- Redundancy/typing guards: `HasSkipCert` assumes `slot ∈ Slots` and well-formed Pool typing. This is enforced elsewhere; adding explicit type preconditions here would be stylistically inconsistent with sibling helpers and unnecessary in TLA+.

## 6. Suggestions for Improvement

- Documentation: Add a brief comment on `HasSkipCert` pointing to Definition 15 (ParentReady) and Table 6 to help readers connect the slot-scoped nature of skip certificates.
- Optional helper symmetry: For readability, consider companion helpers mirroring the full set of certificate existence predicates (already present for notarization, fallback, fast finalization). The current set is already consistent; no functional change is needed.
- Optional invariant usage: Where appropriate, assert `SkipVsBlockCertExclusion` over `pool.certificates[slot]` in modules that rely on `HasSkipCert` (it already appears as a global property in MainProtocol), to surface modeling errors early during proofs.

