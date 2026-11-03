# Balanced finite-point BASE formula supplier

Subject label: `BalancedBoxFormula4`. Source: paper08 `thm:balanced`, especially `08-multivariate-collapse-comparison/paper.tex` lines 1007–1022. The shared-basis grammar is at lines 947–959, the original signed row and threshold at lines 969–982, and the positive raw-variable domain at lines 47, 833 and 848. The source SHA-256 is `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. The accepted finite-table evaluator is the `BalancedBoxEvaluation3` checkpoint `ba676643`, snapshot v48. The accepted small-box and source-adapter statements remain unchanged.

This supplier constructs the literal finite-point part of the balanced comparison, proves its exact finite-box truth and small-branch completeness, preserves the original raw support, calibrates an actual numeric source-code map and proves that map uniformly computable. It does not assemble the recursive balanced compiler, discharge preceding-level large guards, or claim Boolean/quantified arithmetic decidability. No accepted file is modified.

## Deliberate finite-box strengthening

The paper retains finite-box points where both some original complete input is small and the requested sign holds. This supplier instead retains every finite-box point having the requested sign. This is intentional and needs no new numerical complete-input evaluator. Every retained point has its actual source sign, so the extra points are sound and may harmlessly overlap the large branch. The accepted small-box theorem proves that every ambient-positive valuation with some original complete input below the original threshold belongs to this finite box. Thus omitting the additional small-input filter does not omit any small exception.

The exact first target is deliberately stronger than small-branch soundness. For every typed certificate, pair, integer desired sign and raw valuation, without genuineness or positivity premises, the emitted formula is true if and only if:

1. Every raw name in the original pair's ambient support has value strictly between zero and the original `BalancedRow.threshold (comparisonRow E F)`.
2. `Int.sign ((value E : Int) - (value F : Int))` is the requested integer.

The subtraction is in the integers. Requested values other than -1, 0 and 1 select no points. All raw coordinates outside the original ambient support remain unrestricted, including zero coordinates. The additional small-branch equivalence has exactly the accepted hypotheses: a genuine lower certificate, positivity on the original ambient support and the existing original `smallBranch`. No additional top-head validity, independent basis-value or support-survivor hypothesis is added.

## Existing literal BASE syntax and actual point evaluator

`pointFormula support word` is an ordinary `BaseFormula.Formula`. It conjoins, in ascending coordinate position order, literal equations `.equal (.variable (support.getD j 0)) (.numeral (word.getD j 1))`. Its only logical constructors are the existing equality and conjunction, with the existing truth constructor as the empty fold. `sourceFormula` disjoins retained point formulas using the existing disjunction and falsity constructors. Numerals have their existing finite-addition interpretation. There is no new function, relation, head atom, basis-variable sort or opaque semantic predicate in the output.

The support is exactly `BalancedSmallBox.sourceSupport`, namely the deduplication of `rawVariables E ++ rawVariables F` before collection, cancellation or sign filtering. Only raw names are deduplicated. Repeated or dependent common-basis entries, all original atom occurrences and the one original certificate are retained by the accepted evaluator.

The word list is literally `BalancedSmallBox.boxWords`, hence the existing `singleCoreBoxWords` at the original balanced threshold. Its enumeration order is unchanged. Empty support has the single empty word and an empty point is true. For a nonempty support an empty positive interval has no words, with a false disjunction. These are the inherited finite-word conventions, not special-cased semantic exceptions.

The sign filter calls the unchanged `BalancedEvaluation.joint` twice, with the same original encoded certificate and the original left and right expressions. Both calls use the same `BalancedBoxEvaluation.finiteTable support word`. No alternative source evaluator is defined. In particular, sparse raw variable indices remain their original table positions rather than becoming coordinate numbers. The existing first-occurrence lookup supplies the representative values, and the default one off support belongs only to the representative used for evaluation. Source-support stability transfers the two values back to any original valuation agreeing on support; it does not restrict that valuation outside support.

## Numeric code construction and calibration

The raw domain is `Nat × List Nat × Nat × Nat × Nat × Int`, in the explicit order `(k, Γ, C, E, F, desired)`. The shape passed to both unchanged evaluator calls is `k :: Γ`.

- `rawSupport` uses the existing `BalancedEvaluation.codeVariables` on both original codes and then deduplicates their appended ordered support lists.
- `rawWords` is the same `singleCoreBoxWords` algorithm at the existing `BalancedSourceAdapter.threshold k E F`, with the length of that raw support.
- `codeSign` is the integer sign of the two actual `joint` values at the existing `finiteTable`; it has no numerical small-input-list filter.
- `pointCode` uses the existing `CommonHeadCode.conjoin` fold. Its atomic opcode is `(2, 4*i+1, 4*v)`, the actual `BaseTerm.encode` values for variable `i` and numeral `v`. Raw variable names or numerals are not accidentally treated as term codes.
- `formulaCode` filters the exact raw words by that sign and applies the existing `CommonHeadCode.disjoin` to their point codes. The only output tags are literal equality, true, false, conjunction and disjunction from the existing postfix language. Neither head evaluation nor the numeric sign computation is a runtime opcode.

`ActualSourceCodeCalibration` requires literal equalities for the actual encoded typed inputs: raw support equals original source support; the numeric threshold equals the original signed-row threshold; the raw word list equals the typed box word list; and every valid word's computed sign equals the actual typed-source sign at its accepted box valuation. Finally, the numeric output must be exactly `(sourceFormula ...).encode`, not just a semantically equivalent program or an encoding of a newly defined syntax.

`AllCodeComputation` is unconditional `Computable` for that precise numeric `formulaCode` function on all raw inputs. It does not assume a computation-interface hypothesis. The all-input proof must use the accepted uniformly computable `joint` and `finiteTable`, the existing support algorithm, the existing source-adapter threshold algorithm and elementary finite-list operations. Malformed source codes retain the existing decode defaults; no validity claim is made for them. This is a uniform finite-formula constructor, not a numeric recursive compiler or a complexity bound.

## Support and code law

`OriginalSupportAndLiteralCode` contains three statements. First, `pointCode support word` is literally `(pointFormula support word).encode` for arbitrary finite support and word lists. Second, the emitted typed formula's encoded raw-variable list equals that formula's own variable list, and every such variable belongs to the original `sourceAmbient`. Third, on every arbitrary raw input, every raw name found in the numeric output is contained in the original `rawSupport` extracted before filtering.

Containment is the intended claim. Equality with the original support is not generally true because there can be no retained points, in which case the output is falsity. This supplier does not add tautological variables to a false branch merely to assert exact support equality. The only exact variable-list equality is the ordinary code-to-literal-formula encoding law, which preserves repetitions in the emitted formula.

This scope proves the literal syntax's semantic equivalence directly through `Formula.eval` and proves exact identity of its numeric encoding. It does not add a separately frozen theorem for `BaseFormula.evaluate`. The accepted general runtime semantics can be reused later through a thin import interface; no broad `BaseFormulaProof` dependency is required here.

## Four exact targets and absent proof candidates

The separate frozen propositions and aliases are:

1. `ExactFiniteBoxFormula` / `exact_finite_box_formula`: unconditional exact finite-box truth and the genuine-certificate, ambient-positive small-branch corollary.
2. `OriginalSupportAndLiteralCode` / `original_support_and_literal_code`: literal point encoding, code/formula variable-list agreement, original typed-support containment and all-raw-output support containment.
3. `ActualSourceCodeCalibration` / `actual_source_code_calibration`: original support/threshold/word/sign calibration and exact existing postfix output.
4. `AllCodeComputation` / `all_code_computation`: unconditional uniform computability of the actual raw constructor.

The six modular proof candidates named in the freeze specification are absent during this drafting stage:

1. `BalancedBoxFormulaLiteralProof.lean`: elementary point/conjunction/disjunction truth, literal encodings and raw-variable support laws. Reprove the needed short Boolean encoding facts locally rather than import `BaseFormulaProof` or `GuardCodeRuntimeProof`.
2. `BalancedBoxFormulaSemanticProof.lean`: exact finite-box equivalence and the small-branch corollary, using accepted `BalancedBoxEvaluationProof`, `BalancedSmallBoxProof` and the literal lemmas.
3. `BalancedBoxFormulaCalibrationProof.lean`: typed code calibration from accepted `BalancedBoxEvaluation` and `BalancedSourceAdapterSemanticProof`, plus the literal code folds.
4. `BalancedBoxFormulaDataProgramsProof.lean`: primitive-recursive word enumeration and elementary literal point/disjunction-code list operations. It may use the accepted narrow `BalancedBoxEvaluationGraphProof` fold facts and `IntegerAlgorithmsProof`.
5. `BalancedBoxFormulaProgramsProof.lean`: unconditional computation using the accepted `BalancedBoxEvaluationInterfacesProof`, `BalancedBoxEvaluationTableProof`, `BalancedSourceAdapterDataProgramsProof` and the new data-program lemmas. Support computation is extracted from the same accepted `joint` when useful, not replaced by a new algorithm.
6. `BalancedBoxFormulaProof.lean`: aggregate exports of the four exact target proofs.

A static read-only local-import inspection found no `LinkedResidue` dependency in the planned accepted `BalancedSourceAdapterSemanticProof`, `BalancedSourceAdapterDataProgramsProof`, `BalancedBoxEvaluationProof` or `BaseFormulaDefinitions` closures. In contrast, `BaseFormulaProof` reaches a broad closure through `GuardCodeRuntimeProof` and `CommonHeadCompilerProof`; those three proof imports are excluded, as are the earlier broad `BalancedEvaluationInterfacesProof` and `BalancedEvaluationCalibrationProof` suppliers. This inspection is not a compilation or memory-success claim.

The immutable compiler wrapper, resource caps, exact-target comparison and actual axiom-closure audit remain mandatory after root review, comparator approval and freeze. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. There are no new axioms, theorem-valued fields, oracles, `sorry`, `admit`, `native_decide`, accepted-file edits, candidate authoring, compiler runs or Git operations in this draft.
