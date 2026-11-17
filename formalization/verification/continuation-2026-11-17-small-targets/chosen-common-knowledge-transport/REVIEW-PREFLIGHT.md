# Independent preflight review — chosen common-knowledge transport

Decision: **accept the frozen supporting scope**. Reviewed against branch base
`73709637b4997891d26ad5651628a44a8ac38392` on 2026-11-17.

## Frozen statements

- `Targets.lean`: `4d9447fe713ed4c9b8ccafdc21e0e2f62d38762c7831c804fbfb0dd3a71e51af`.
- `ComparatorGate.lean`: `c59c01088756c3b075eb31b68f2114b5a16fa7ab022e67072b3e86444fb31c0c`.

Both hashes independently match `FROZEN-COMPARISON.json`. The comparator
retains the literal displayed-theta and top-selector-theta ASTs separately.

## Source correspondence and proof viability

`ImplicationTransport` keeps one actual source D, the same source parameters,
and the same chosen retained-parameter common-knowledge formula. It accepts
an actual ordinary D derivation of `sigma -> tau` and concludes an ordinary
D derivation of `CK_A(sigma) -> CK_A(tau)`, for arbitrary full-language
sentences and selectors. The original internal HB2/HB3 derivations remain
explicit conditional hypotheses; they are not new axioms or hidden oracles.

The proof can use the existing Lob reduction on
`delta = CK_A(sigma) -> CK_A(tau)`. Selected reflection gives `E_A(delta)`
from `Pr_D(delta)`. The source fixed point gives `E_A(sigma)` and
`E_A(CK_A(sigma))`. Certification of the given implication and selected
distribution give `E_A(tau)`; selected distribution of delta gives
`E_A(CK_A(tau))`. The target fixed point then proves the implication, and
Lob discharges its provability hypothesis.

`DisplayedThetaReverse` is valid in every ordinary theory: the top selector
is the reflexive equality guard, so its extra guard is discharged by equality
reflexivity. The existing `LiteralProof.displayedThetaBridge` supplies the
opposite implication. `DisplayedCommonKnowledge` transports both directions
through the same chosen CK formula without identifying sentence codes.

No existing arbitrary-sentence chosen-CK implication transport was found.
The existing collapse result is specialized to selector contradiction
sentences and does not discharge this target.

Semantic source pins:

- `12-common-knowledge-necessitation/paper.tex`:
  `7837a0498407b5f9b2a892d6478f02f250943ae62ff69649474700cef89bb4bc`.
- `GorbowUniformCommonKnowledgeDefinitions.lean`:
  `e9c26375726cb978924177c87418ad977de46aea7e731f034dcfe327c47f5dab`.
- `CertifiedSourceProvabilityCompletion/LiteralDefinitions.lean`:
  `30d159d40971ab2e172fbcf6eefbf7c65b513c828f86bc01485bb7cc3d1b7b66`.

## Verification and limits

This is a source/type review, not a native proof acceptance. The reviewer
launched no compiler. Candidate compilation must use the existing serialized
checker and unchanged limits, followed by exact-type and actual-axiom audits.

The packet addresses the unnumbered `eq:counterexample` distinction explicitly
excluded from `SameSourceNumberedIntegration.Targets.Source`. Its conditional
transport alone does not establish an unconditional literal counterexample,
choose an actual source witness, discharge internal HB, or prove KT/KT+UBF
nonprovability. Those require the existing same-tuple HB specialization and
the later KT negation/consistency assembly. No numbered promotion follows.
