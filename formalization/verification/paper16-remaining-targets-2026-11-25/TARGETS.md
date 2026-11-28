# Remaining public paper targets

Applies to the current comparison register at reconciled tip `2391fb243`
and the continuation on `formalization/paper16-continuation-2026-11-25`.
The seven pending statements at branch selection were all in Paper 16.
The earlier register also has one pending statement in live
Paper 02. Its other eight pending rows belong to the archived Paper 06
edition. The modules below give proof destinations and exact interfaces.
Use the corresponding named statement as the next proof's conclusion.
A supporting lemma advances the plan when it discharges an identified
premise or supplies a named bridge.

- [Paper 16 structural scope](../../LogicLineages/PersistentMarking/Paper16StructuralScopeTargets.lean)
- [Paper 16 realization direction](../../LogicLineages/NativeModule/PersistentMarking/Paper16RealizationDirectionTargets.lean)
- [Paper 16 arithmetic accessibility V2](../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneTargetsV2.lean)
- [Paper 16 ordinal calibration and assembly](../../LogicLineages/NativeModule/PersistentMarking/Paper16RemainingOrdinalTargets.lean)
- [Paper 02 further consumers](../../LogicLineages/ComputabilityKnowledge/Paper02FiniteVectorConsumerTargets.lean)

## Numbered statements

| Manuscript claim | Lean target | Work needed for adoption |
| --- | --- | --- |
| `lem:structural-interpretation`, `decision.tex:149` | `Paper16StructuralScopeTargets.StructuralInterpretationWithBoundary` | Package the retained-stage laws, named substitution, valid concrete frame, canonical finite frame, and consumed prefix. Compare the finite covered syntax to the manuscript and attach the existing availability-gap witness for the bottom-family sentence. |
| `lem:arithmetic-accessibility`, `ordinals.tex:79` | `Paper16AccessibilityMilestoneTargetsV2.InstalledArithmeticAccessibility` and `ConditionalUpperUniformTargets.UniformAccessibility` | Select one legal installed window for every closed source window. Derive all-terms internally there, and carry the same programs and calibration to the uniform numbered interface. |
| `thm:upper`, `ordinals.tex:315` | `Paper16RemainingOrdinalTargets.UpperAtCitedOrdinal citedBH` and `ConditionalUpperTargets.UpperStatement citedBH` | Discharge uniform accessibility for the conditional upper bound. The printed result also needs the cited inductive-norm theorem at that ordinal. |
| `lem:realization`, `ordinals.tex:434` | `Paper16RealizationDirectionTargets.PrintedDirectionCounterexample`, a diagnostic for `PrintedRealization` | Refute the literal direction at a closed native edge. The existing backward closure matches the beta argument at `ordinals.tex:447–448` and supplies the candidate for explicit wording. |
| `lem:tower-cofinality`, `ordinals.tex:612` | `Paper16RemainingOrdinalTargets.CofinalityAtCitedOrdinal citedBH` | Reuse the checked supremum-to-endpoint equality. Supply an independent source definition of the cited ordinal and prove its agreement with the endpoint. |
| `thm:height`, `ordinals.tex:634` | `Paper16RemainingOrdinalTargets.HeightAtActualEndpoint`, then `ConditionalHeightEffectiveTargets.HeightIsBHEffective citedBH` | Full tower calibration and the upper bound. Keep the closed native `o → o` witness sequence and its rank comparison. |
| `thm:main`, `paper.tex:96` | `Paper16RemainingOrdinalTargets.PrincipalAtActualEndpoint`, then `ConditionalMain16UniformEffectiveCodedTargets.Main16StatementCodedEffective citedBH` | Assemble the earlier items with typed closed native witnesses and the primitive-recursive code of their actual sequence. Use the cited endpoint identification for the printed ordinal. |
| Paper 02 `cor:consumers`, `02-exponential-comparison/paper.tex:498` | `Paper02FiniteVectorConsumerTargets.FurtherExactConsumersAtPublishedControl` | Extend the checked exponential-fragment consumers to the finite-valued original O input promise, including collapse nodes. The broader affine reading has its own companion target. |

## Proof checkpoints

### Structural correspondence and realization

- `NamedValueSubstitution` quantifies over all retained stages and the
  actual finite support. Use `FreeSubstitution` and
  `GraftingProof.typedNamedSubstitutionEncoding` to reach named syntax.
  The images come from the typed ordinary source map, which may introduce
  new free names.
- `RelatedFrameFixedApplication`, `NamedFixedApplication`, and
  `ConsumedPrefixFixedApplication` refer to the full substituted source
  and actual argument tuple. Existing providers are
  `exact_NamedFixedConcreteWholeCall`, `exact_CanonicalNamedWholeCall`, and
  `exact_CanonicalConcretePrefixCall`. The destination is evaluated in its
  literal context. `concreteOutput` handles the undefined case. The
  fixed-point premise belongs to these applications.
- `PrintedDirectionCounterexample` asks for one closed native base edge.
  A candidate is `(λy : σ. y) t  →  t`, where `σ = o → o` and
  `t = λx : o. x`.
  A countable ordinal between the two strict ranks separates realization.
  The existing `BackwardRealization` interface retains the direction
  used by the beta and finite-chain proofs. Decide the manuscript wording
  before promoting the numbered row.

### Internal accessibility

The active target is `Paper16AccessibilityMilestoneTargetsV2`. It uses
the existing `formulaType` conversion from the source types in `K` to
the types accepted by object-language typing and computability formulas.
The [original target](../../LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneTargets.lean)
is retained. The V2 declaration and conditional `CloseAllTerms` and
`InstalledToUniform` bridges passed native checks. Their source
correspondence and receipts are recorded in
[the V2 handoff](../local-fable-continuation-2026-11-25/2026-11-26/native-window-v2-rebase.md).

All these checkpoints use the V2 `InstalledWindow` at the same closed
`S, K`, selected probes, and outer-context numeral. The current
[three-lane handoff](../local-fable-continuation-2026-11-25/2026-11-26/HANDOFF.md)
records the checked concrete program replacements and the exact
remaining arrow, beta, and lambda obligations.

1. Discharge `SelectInstalledWindows`. Install the actual
   `rawWithTarget` and `addressPositive` over the same
   scalar, guards and least programs as the original window. The
   `InstalledTupleAt` field also pins `jRaw`, the certified `dCore`,
   and the application/probe inputs. Existence for every closed `S, K`
   includes the mixed-window selection problem.
2. Prove `ApplicationArithmetic` at that selection. Its four fields are
   backward matching, forward transport, total typed probing, and
   computability of the actual selected fresh variable. The installed
   tuple already supplies total typed probing. Apply the existing
   downward-closure and pullback theorems on that very presentation.
3. Use `CertifiedMultisetUnion` with the installed permutation observer.
   The order-sensitive list split has a checked counterexample.
   Supply `MultisetGeneration` for selected singleton, member and union
   programs, including `UnionFeedsCountedReport` on the same union code.
   `FinishMultisets` asks for singleton and member accessibility from
   counted closure and those generation laws.
4. Close `TypedCarrierComputability` by the manuscript's neutral, lambda,
   constructor, and structural inductions. The lambda premise needs
   preservation of an open raw certificate under the actual singleton
   instance program, with either an accepted resulting path or the
   allowed collapse to equality. The currently drafted literal rows
   handle selected dispatch cases; the recursive substitution and raw
   preservation premises remain proof work. Constructor reduction uses
   the complete eight-rule exhaustion at the selected typed address.
5. Discharge `CarrierTypingCases` for admitted addresses. Use
   `CloseAllTerms` at the same context to assemble the internal sentence,
   then instantiate `InstalledArithmeticAccessibility`. The
   `InstalledToUniform` bridge projects the calibrated four
   programs. The existing uniform-to-individual bridge supplies the
   numeral membership instances used by the upper bound.

### Ordinal inputs and assembly

1. The arithmetic and omega equations are bundled as `OrdinalSemantics`.
   Discharge `OrdinalSemanticsExistence` using
   `ActualCollapseMain.SolutionExists`.
   `veblenData` is the actual clause-(P) collapse.
2. Calibrate at `n = 3` through the existing
   `ActualCalibrationThree.PsiPowerLevel` and `CalibrationThree` targets.
   The checks for `n = 0, 1, 2` are existing suppliers. The fixed
   pointwise target is `AllTowerCalibration`, which compares the
   exact native tower and actual collapse for every `n` using the same
   operations. It supplies `CalibrationForAssembly`, which uses the
   existing existential interface.
3. Establish `NormAtActualEndpoint`, or first establish
   `ExternalOrdinalInterfaceID1Targets.NormTheorem citedBH` for the
   independently defined ordinal and `IdentifyCitedEndpoint citedBH`.
   The latter Lean target deliberately exposes the missing independent
   ordinal definition at its argument boundary. Endpoint equality alone
   supplies neither the inductive-norm theorem nor the source identity.
   `LeastNormBound` names an independent arithmetic candidate. A source
   theorem must identify that candidate with the cited ordinal before
   it can fill this role.
4. Use `UpperAtActualEndpoint`, `CofinalityAtActualEndpoint`,
   `HeightAtActualEndpoint`, and `PrincipalAtActualEndpoint` in order
   of dependency. The `ActualCollapseMain` assembly supplies the
   existing conditional proofs. The printed statements also use the
   independent identification.

### Paper 02 further consumers

1. Work on the original prefix codes of nonempty finite-valued O-vectors.
   The programs receive codes and arities. They must answer on true and
   false cases under the finiteness promise, without a finiteness witness
   as a program input.
2. Prove `MultivariableEquality`, `UnaryComparison`, and
   `UnaryBoundedNorm`. The comparators retain the original admissible
   substitutions, zero padding, strictness at component zero, and the
   norm bound relative to component zero. The checked affine comparison
   on positive exponential expressions supplies the last conjunct of
   `FurtherExactConsumersAtPublishedControl`.
3. If the affine sentence is read over all finite-valued O-vectors,
   discharge `AffineFiniteVectorComparison` as well. Compile the affine
   coordinate substitution on the original codes, including their
   collapse nodes. Use the existing denotational substitution theorem
   and preservation of the finiteness promise, then apply the unary
   vector decider.
4. The source-indexed semantics uses the published example
   `Φ(n) = F₅(n+100)`. A proof claimed for every permitted control needs a
   parameterized target and a source decision about that quantifier.

## Validation

The current comparison register has **161 checked / 6 pending**.
`Paper16RealizationDirectionTargets` passed the native declaration check
(receipt `1795666861166467569-12` in the older checkout's
`formalization/build-reports/`). The run used the new target file and
148 byte-identical dependency sources at the path of the existing
checked cache, with the same Lean toolchain and package manifest.
The other new target modules still require their native declaration checks.

- `Paper16StructuralScopeProof.exact_StructuralInterpretationWithBoundary`
  passed native checking. It assembles the named and bound substitution
  interfaces, all three fixed applications and the bottom-family witness.
  Receipt `1795672039102686067-2` records the exact proof source hash.
  The [source comparison](STRUCTURAL-SCOPE-ACCEPTANCE.json) supports
  adoption of the numbered structural interpretation row.
- `Paper16RealizationDirectionProof.exact_PrintedDirectionCounterexample`
  and `exact_NotPrintedRealization` passed native checking in receipt
  `1795671863201769769-10`. The countable rank of the closed beta source
  realizes a value that its strict reduct fails to realize. The printed
  closure row remains pending a wording decision. `BackwardRealization`
  is the direction used by the manuscript's beta argument.

The two new proof modules were checked with a source-matched import cache
and the pinned toolchain. Their axiom audits report `propext`,
`Classical.choice` and `Quot.sound`. The receipts and logs are in
`formalization/build-reports/`. The cited ordinal still requires an
independent source identification.
