# thm:ground / thm:main assembly — source map (Opus A, task 6, 2026-11-22)

Modules in `LogicLineages/PermittedControl/`, prefix `GroundComparison`:

- `GroundComparisonDomainTargets/Proof` (M1): `SelectedGroundDomain`. For ground Γ, the admissible
  substitutions at a selected control are exactly the positive natural valuations.
- `GroundComparisonPositiveTargets/Proof` (M3): `positiveTest` on `closedPositiveCode` lists, through
  `encodedClosedPositive` and `rawComparisonCode`, with zero padding. `ExactPositiveTest` gives the iff with the
  padded ordinal values; `PositiveTestEffectivity` is `Primrec`.
- `GroundComparisonTargets` (M2): the `thm:ground` comparator `GroundComparison` (see
  `P17-THM-GROUND-CORRESPONDENCE.md`).
- `GroundComparisonReductionTargets/Proof`: `ExactCanonicalReduction`. `Canonical` holds iff the raw positive test
  passes and there is no positive shared-input scalar counterexample (`GroundScalarCircuit.Counter`). Its hypotheses
  are the per-term clauses of #261 `TypedImage`.
- `GroundComparisonAssemblyTargets/Proof`: `QueryInterface` is the M4 interface verbatim; `ExactGroundFromQuery`
  turns any computable compiler meeting it into `GroundComparison`. Suppliers: #261 `typedImage`/`Programs`,
  `scalarSyntaxNormalizationCorrect`, and `StageCallbackGuardRender.closedBlockDecision` (#1418).
- `GroundComparisonMainTargets` (`thm:main` comparator `MainComparison`; see `P17-THM-MAIN-CORRESPONDENCE.md`).
- Final theorems: in `GroundComparisonProof`/`GroundComparisonMainProof`, once Opus B's code-level M4
  (`GroundScalarCircuit.ExactQueryCode`, `QueryCodeEffectivity`) is gated.

Not claimed: anything about policies not meeting `PolicyShape.Effective`, raw codes that are not term
encodings, or a single procedure uniform in the policy or in `b`.
