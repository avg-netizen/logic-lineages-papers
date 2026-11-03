# Balanced actual-source guard descent supplier

Subject label: `BalancedGuardDescent5`. Source: paper08 `thm:balanced`, especially `08-multivariate-collapse-comparison/paper.tex` lines 1004–1026. The actual shared-basis grammar is at lines 945–959, the signed row at lines 969–974 and the original threshold `eq:balanced-L` at lines 980–982. The source SHA-256 is `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This follows the accepted `BalancedBoxFormula121` checkpoint `b63c335b`, snapshot v52, without modifying that supplier or any other accepted file.

This is a bounded supplier for the paper's statement that all large-branch guards and the all-canceled remainder are comparisons of preceding-level affine expressions under their preceding-level certificate. It translates the already accepted large guard assuming a correct lower comparator, preserves original support under a separate explicit support premise, and gives exact numeric child/assembly interfaces. It does not define a recursive balanced compiler, discharge its lower-comparator induction premise, combine large and finite-box branches, or claim the whole balanced comparison or quantified decision theorem.

## Actual lower syntax and exact translation

`Lower Γ` is a typed map from two existing `BalancedSyntax.Syntax Γ` terms and an integer requested sign to the existing `BaseFormula.Formula`. It does not add any new runtime symbol or semantic oracle. `translateGuard` operates on the existing `CommonHeadLargeGuards.Formula`, retaining every Boolean constructor:

- Equality invokes the lower comparator on the two actual label terms with requested sign zero.
- Strict order invokes it with requested sign minus one.
- A lower-bound guard `c ≤ label i` becomes the literal negation of the lower comparison `label i < Affine.numeral Γ c`.
- Truth, falsity, negation, conjunction and disjunction retain their literal structure.

Every out-of-range label has the actual source default `Affine.numeral Γ 0`. A label represents the full complete input, including its head norm, or one of the actual lower parts. Therefore no head norm is subtracted from a bound, no new or larger threshold is used, and even bound zero emits the same literal negation. The common-layer `constantCode` belongs to a different source grammar and cannot be reused: at a nonempty balanced shape the actual numeral code contains the complete length-k zero outside vector and empty atom list. The numeric layer uses the accepted `BalancedAffineCode.numeral` instead.

## Visible induction domain and support premises

`LowerCorrect Γ lowerC lower ν` is explicitly quantified over genuine lower expressions and requested integer signs, with positivity required only on each compared pair's actual raw support. The lower certificate `lowerC` and raw valuation `ν` are fixed and identical on both sides. It does not require correctness for nongenuine heads, global positivity of `ν`, an independently valued common basis, or a new certificate per guard.

The generic semantic target requires every supplied label to be genuine and `ν` to be positive on `labelSupport`, the concatenated actual support of those labels. Existing numeral genuineness and empty numeral support pay the bound/default/dummy terms. Existing support membership pays positivity for each invoked pair. This premise matches the intended final induction domain: lower correctness on genuine pairs with their own actual support positive, even when some unrelated raw coordinates are zero.

Semantic correctness cannot imply syntactic support containment. `LowerSupport Γ lowerC lower` is a separate visible premise saying that each emitted lower formula uses only the original two lower terms' raw names. It is a structural statement on all typed terms, independent of genuineness and valuations. The generic support target concludes containment in `labelSupport`. It does not claim equality with the original support, since truth, falsity and simplified guards can omit names.

## Accepted source instantiation

`sourceTranslation` uses exactly `BalancedLargeGuards.sourceTerms k Γ C E F`, in its accepted order: one actual `Affine.completeInput` per original signed atom occurrence, then the literal `Affine.lowerPart E` and `Affine.lowerPart F`. Its guard is exactly the accepted `BalancedLargeGuards.sourceFormula E F desired`. No occurrence is collected, reordered, canceled, or dropped by this supplier.

`ActualSourceDescent` uses `LowerCorrect Γ C.1 lower ν`. Its semantic hypotheses explicitly include genuine `C`, genuine top expressions `E` and `F`, and positivity on the original pair's `BalancedLargeGuards.sourceAmbient`. The proof must obtain genuine labels from the accepted `sourceTerms_genuine` lemma and label support containment from `sourceTerms_support`; those facts are not new user-supplied premises. The same `C.1` and `ν` evaluate every complete input and both lower parts. Positivity on their actual support follows by restriction from the original ambient support, with no condition outside it.

The semantic conclusion first equates the translated formula with the exact accepted guard evaluated at `sourceValuation`, then equates it with the original-threshold large branch and actual signed source comparison. The original threshold is `BalancedRow.threshold (comparisonRow E F)`, imposed on every original atom, including canceled occurrences. The actual source sign is integer subtraction of the two natural-valued source expressions. The all-canceled branch therefore compares the two genuine lower parts, not independent variables or precomputed values.

The source support conclusion has its own `LowerSupport Γ C.1 lower` premise and needs neither genuineness nor positivity. Accepted `sourceTerms_support` proves containment in the same original ambient support. The final recursive compiler must separately discharge both the semantic and structural lower premises by induction; this supplier cannot be counted as that final construction.

## One numeric child per original postfix instruction

The numeric comparison-call input is `(Γ, lowerC, E, F, desired)` of type `List Nat × Nat × Nat × Nat × Int`. Shape is source shape, not a fixed-head list. Certificate and terms use the existing `BalancedEvaluation.encodeCertificate` and `encodeSyntax` codecs.

`typedChild Γ labels q` names the two actual source terms and requested sign for each existing postfix instruction. Tags two and three request the corresponding label comparison. Tag four requests label-versus-actual-numeral strict order. Every other instruction has the harmless literal zero-versus-zero equality child. `child` is the numeric realization using `BalancedAffineCode.numeral` and the same encoded lower certificate for every call. `ExactPostfixSubstitution` requires exact equality between each numeric child and `encodeCall` of that typed child, for all instruction triples and all indices, not merely those inside a valid formula or label range.

`typedResults` maps every original instruction, in order, to the exact existing BASE encoding of the supplied typed comparator's result for its typed child. It supplies no raw decode comparator and no computation assertion about an arbitrary comparator. Its length must equal the original code length.

`instructionCode` substitutes the corresponding child result for equality and strict order. For every bound it appends the existing negation instruction `(5,0,0)`, even when the bound is zero. All Boolean commands and other raw instructions are preserved verbatim; their dummy child results are ignored. `assemble` zips original commands with supplied result lists and flattens in the original order. Exact substitution is asserted on a formula's actual encoding with exactly its `typedResults`; it is not asserted for arbitrary unrelated or truncated result lists.

The postfix target requires literal equality with `(translateGuard Γ lower labels p).encode` for every existing guard formula `p`. Equivalent truth values or a newly defined output language would not meet this target. The short Boolean encoding/list facts should be proved locally rather than importing the broad accepted runtime or comparison-effectivity proofs.

## Actual source calls, strict descent and raw effectivity

`sourceChildren` uses exactly the accepted `BalancedSourceAdapter.lowerCertificate`, `termCodes` and `formulaCode`. The actual-source target must calibrate the numeric child list to the original source formula's encoded instructions mapped to `encodeCall Γ C.1 (typedChild ...)`. Its assembly clause uses the identical typed result list and requires the exact encoding of `sourceTranslation`. Thus the real lower certificate, ordered literal terms, existing source guard code and emitted BASE code are connected by equality, not a convention outside the frozen proposition.

Every original postfix instruction has one child. The source-child list length equals the original adapter guard-code length. Every child has shape `Γ`, so its `measure` is strictly less than the caller shape length `(k :: Γ).length`. This strict decrease is required on all raw source inputs, including ignored Boolean children and malformed certificate/expression codes. The accepted raw defaults are retained; malformed codes are not claimed genuine source encodings.

`UniformPrimitiveRecursive` is unconditional on all raw shapes, certificate codes, source codes, labels, instruction triples, requested signs and result lists. It covers `labelCode`, `child`, `children`, `instructionCode`, `assemble`, `sourceChildren`, `sourceAssemble` and `measure`. The accepted affine numeral and source-adapter primitive-recursive programs supply the numeric ingredients. No lower semantic comparator, source-validity assumption or primitive-recursion witness appears as a premise. A recursive balanced compiler and its overall computability remain separate obligations.

## Five exact targets and proposed proof files

1. `ExactGuardTranslation` / `exact_guard_translation`: generic exact semantics with genuine, support-positive labels; separate support containment under `LowerSupport`.
2. `ActualSourceDescent` / `actual_source_descent`: accepted actual-source guard and large-branch semantics under `C.1`, and original ambient support containment.
3. `ExactPostfixSubstitution` / `exact_postfix_substitution`: exact numeric typed-child calibration, exact result-list length and literal postfix substitution.
4. `ExactActualCallsAndDescent` / `exact_actual_calls_and_descent`: all-raw child count/strict shape decrease and actual-source child/assembly calibration.
5. `UniformPrimitiveRecursive` / `uniform_primitive_recursive`: the unconditional all-raw numeric interface.

The four proposed candidates are absent during this draft:

- `BalancedGuardDescentSemanticProof.lean`: local formula induction, genuine/default/numeral and support facts, then accepted source-label and large-guard semantic instantiation. Use narrow `BalancedAffineSyntaxClosureProof`, `BalancedAffineSyntaxDescentProof`, `BalancedLargeGuardsLabelsProof` and `BalancedLargeGuardsSourceProof` as needed.
- `BalancedGuardDescentCodeProof.lean`: local postfix-list substitution, actual numeral/label code calibration from `BalancedAffineCodeCalibrationProof`, source adapter calibration from `BalancedSourceAdapterSemanticProof`, and child shape/length laws.
- `BalancedGuardDescentProgramsProof.lean`: explicit raw primitive-recursive maps using `BalancedAffineCodeProgramsProof` and `BalancedSourceAdapterProgramsProof`.
- `BalancedGuardDescentProof.lean`: aggregate exports of the five exact target proofs.

A static read-only local import traversal found no `LinkedResidue`, `BaseFormulaProof`, `GuardCodeRuntimeProof`, `CommonLayerEffectivity` or `ComparisonAssembly` dependency in these planned accepted proof suppliers. The new definitions avoid importing `BalancedSmallBoxDefinitions` merely for its positivity abbreviation: explicit support-positivity propositions keep the narrow closure and do not pull in `SingleCorePresburgerDefinitions` or `ComparisonAssemblyDefinitions`. This is only a static import observation, not a compilation or resource-success receipt.

The candidate files remain absent until exact target review and freeze. The immutable compiler wrapper, serialized resource caps, exact-target comparison and actual axiom-closure audit remain required. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. No new axiom, theorem-valued field, oracle, `sorry`, `admit`, unsafe shortcut, accepted-file edit, candidate authoring, compiler run or Git operation belongs to this drafting step.
