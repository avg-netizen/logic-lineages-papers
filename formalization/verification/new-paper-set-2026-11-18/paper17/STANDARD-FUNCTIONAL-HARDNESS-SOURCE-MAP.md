# Unchanged-control functional hardness: source scope of the Phi chain

Source: 17 hardness.tex 244–265, `cor:standard-functional-hardness`. The weak
and strict undecidability statements of `thm:functional-hardness` hold for the
unchanged control G(n)=F_5(n+100), with finite-query internal level two and
single-query internal level three. The printed proof observes that no
count-residue or modular-potential statement occurs in the source compiler,
alignment, detector or undecidability reduction, so those constructions apply
literally with f=G.

Lean: `Phi n = fastControl 5 (n+100)` (OrdinalComparison/ControlDefinitions).
The accepted selected-control endpoints all carry `SelectedWithThreshold ctrl K`,
which Phi does not satisfy, so nothing selected-premised is specialized. Each
layer is restated at Phi and reproved on standard-control suppliers.

| Layer | Comparator | Relation to the accepted selected comparator |
|---|---|---|
| Seeded compiler | StandardSeededCompilerTargets (frozen by the previous coordinator, pre-scope approved) | ctrl := Phi, hypothesis removed, four families |
| Seeded system | StandardSeededSystemTargets | SelectedSeededSystemTargets with ctrl := Phi, hypothesis removed, six families |
| Single query | StandardSingleQueryTargets | SelectedSingleQueryTargets with ctrl := Phi, hypothesis removed, five families (three control-free) |
| Corollary | StandardFunctionalHardnessTargets | SelectedFunctionalHardnessTargets with ctrl := Phi, hypothesis removed, eight clauses |

The definitions under the comparators are the existing control-parametric ones
(`AdmissibleSubstitution`, `groundValue`, `Solves`, `universalStrict`,
`universalWeak`, `GroundComparison`, `FiniteQueryReduction`,
`SingleQueryReduction`, `HasComparisonDecider`) evaluated at Phi. Deciders
range over all actual sources within the printed level bounds; reductions are
the literal total programs `FiniteQueryCode.reduceCode` and
`SeededQueryCode.reduceCode`.

Suppliers used at their actual scope:

- Standard-control (Phi) proofs: StandardPairCompiler algebra, StandardOmegaSeed
  (actual scaled closed-seed pair), StandardFunctionalDetector values/detector/
  alignment, StandardSystemMask renaming and alignment lemmas,
  StandardAggregation (aggregateAt, aggregateWeakQuery, groundResult),
  StandardFiniteQuery (accepted packet 379).
- Arbitrary-control public theorems with no selected hypothesis:
  `SelectedSeededCompiler.Proof.seeded_family`, `exactSeedSubstitution`,
  `seededInputs_eq_lastCases`, `SelectedOmegaSeed.Proof.closedSeed`,
  `SelectedDecisionPullback.Proof.finiteQueryPullback`,
  `SelectedFunctionalHardness.Proof.singleQueryPullback`.
- Control-free: seeded code programs/calibration/well-formedness, level-three
  bounds, the polynomial undecidability supplier, empty/zero-system
  satisfiability facts.

Private embedding/projection helpers of the selected solvability proof are
reconstructed verbatim in StandardSeededSolvabilityProof; they mention no
control. No selected-control membership, generated-only valuation restriction,
caller-supplied success, decider oracle or new premise is introduced.

Not covered: `prop:threshold`, `thm:ground`, `thm:arithmetic`, `thm:main` and
the remaining paper17 statements.
