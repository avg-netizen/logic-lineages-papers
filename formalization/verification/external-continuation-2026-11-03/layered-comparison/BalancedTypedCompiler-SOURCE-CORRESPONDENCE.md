# Balanced typed recursive BASE-formula construction

Subject label: `BalancedTypedCompiler3`. Source: paper08 `thm:balanced`, in the reviewed window `08-multivariate-collapse-comparison/paper.tex` lines 937–1030. The actual shared-basis grammar is at lines 945–959, the theorem at lines 961–966, the signed row and original `eq:balanced-L` at lines 969–982, the lower guards at lines 1004–1005 and 1020–1021, and finite-box/certificate induction at lines 1007–1026. The inherited positive raw-variable domain is explicit in the preceding definition of the same level-zero class at lines 833–835. Source SHA-256: `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This draft follows the verified `BalancedRawCompiler3` save `b85b94dd6100f199ea69ee6707beac5161a62c4d` without changing an accepted supplier.

This component connects the accepted unconditional raw compiler to an actual recursively defined ordinary BASE formula, proves original-support containment and closes the actual-source semantic induction. It is not an existential extraction of a formula from a semantic claim. Exact equality of the emitted free-variable set with the original pair support remains PENDING, as do the quantified BASE decision supplier and the complete balanced theorem. No whole-balanced numbered target is promoted by these three obligations.

## Literal typed construction

`typedFormula` has type `(Γ : List Nat) → Certificate Γ → Syntax Γ → Syntax Γ → Int → BaseFormula.Formula`. Its recursion is on the actual finite source shape `Γ`, not a certificate-validity proof, arbitrary lower-comparator oracle, formula witness or numerical decoder. The definition applies to every typed certificate and source pair, including data with nongenuine heads, and every integer requested sign.

At shape `[]`, the two terms are the actual existing `CommonLayerSyntax.BaseTerm` operands. The result is exactly `BalancedRawCompiler.baseFormula E F desired`: equality for zero, forward strict order for minus one, reversed strict order for one, and literal falsity for every other integer. No independent valuation of term labels is introduced.

At shape `k :: Γ`, the formula is the literal existing `BaseFormula.Formula.disjunction` of:

1. `BalancedBoxFormula.sourceFormula k Γ C E F desired`;
2. `BalancedGuardDescent.sourceTranslation k Γ C E F desired (fun G H d => typedFormula Γ C.1 G H d)`.

The original finite-box formula is first and the translated original large guard is second, exactly matching the accepted raw compiler's output order. Every lower guard compares its actual lower terms under the unchanged original certificate `C.1`. The accepted source guard retains the original complete inputs and lower parts, the original threshold, and all original occurrences. Repeated or dependent basis entries and shared raw names remain correlated through that certificate and the single original valuation.

The construction introduces no extra BASE predicate, collapse instruction, evaluator instruction, term-value parameter, alternative Boolean encoding, larger threshold or new word enumeration. Its `noncomputable` marker reflects the already accepted finite-box evaluator, not a choice of output formula. The independently accepted raw `BalancedRawCompiler.compileCode` and its unconditional all-code computability supply effectivity once exact encoding calibration is established.

## Exact all-typed encoding calibration

`ExactTypedCodeCalibration` requires, for every shape `Γ`, typed certificate `C`, typed source pair `E,F` and integer `desired`, literal equality

`BalancedRawCompiler.compileCode Γ (encodeCertificate Γ C) (encodeSyntax Γ E) (encodeSyntax Γ F) desired = (typedFormula Γ C E F desired).encode`.

There is no genuineness, positivity, lower-correctness, lower-calibration or computability premise. This identifies the previously accepted specific raw all-code constructor with the actual ordinary formula's existing postfix encoding, not merely with a code having the same truth value.

The intended induction uses the accepted actual BASE leaf from `BalancedRawCompilerCallProof`. At a positive shape, accepted `BalancedBoxFormula` calibration pays the first branch. `BalancedGuardDescentCodeProof.exactActualCallsAndDescent` identifies the exact original numeric child list with the encoded typed calls and identifies substitution of the typed result list with the encoding of `sourceTranslation`. Applying the induction hypothesis to every lower typed child under `C.1` gives exactly those typed result codes, in the existing order, including the ignored Boolean children. A local literal disjunction-encoding identity joins the two branches. No raw-code roundtrip for arbitrary malformed inputs is asserted; all-code raw computation has already been proved separately.

## Independent original-support induction

`OriginalSupportContainment` requires every variable occurring in the actual emitted formula to belong to `rawVariables Γ C E ++ rawVariables Γ C F`. This is the original pair's syntactic raw support, before sign filtering, block collection or cancellation. The target holds for all typed `C,E,F,desired`, independently of genuineness, source truth or valuation.

The empty-shape case follows directly from the literal BASE leaf; reversing strict order only swaps the two operand-support lists. At an upper shape, the accepted finite-box support theorem gives containment for the first disjunct. The induction hypothesis for all lower typed pairs establishes `BalancedGuardDescent.LowerSupport Γ C.1 (fun G H d => typedFormula Γ C.1 G H d)`. The accepted guard source-support theorem then gives containment for the second disjunct in the same original ambient support. `LowerSupport` is thus discharged internally, not retained as a target premise and not inferred from semantic correctness.

This containment does not claim that every original name occurs in the output. Sign filtering, truth, falsity and empty/irrelevant branches can omit names. The source theorem's **exact same-free-variable equality** clause remains explicitly PENDING. The separately approved later direction is a literal `x = x` padding wrapper for the original support, with its own exact code, truth, support-equality and effectiveness obligations. No such wrapper is defined or claimed here; in particular, desired signs outside `{-1,0,1}` do not silently acquire original variables in this component.

## Actual sign semantics and the original positive domain

`ActualSignSemantics` quantifies over every actual shape, typed certificate, typed pair, integer desired sign and raw valuation `ν : Nat → Nat`. Its only semantic premises are `genuineCertificate Γ C`, `genuineExpression Γ E`, `genuineExpression Γ F`, and `0 < ν i` for each `i` in the original pair support. It concludes that the emitted ordinary formula is true exactly when `Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = desired`. The subtraction is in integers; no truncated natural subtraction is used.

Positivity on actual support is the source's positive raw-variable domain, not an extra global restriction. The balanced grammar reuses the positive level-zero class from lines 833–835, and the proof enumerates `[1,L-1]^V` at lines 1015–1018. Coordinates outside the original support are unrestricted and may be zero. The finite-table representative's outside-one default does not become a premise on `ν`. Empty support needs no positive coordinate and retains the accepted single empty valuation.

The empty-shape case uses the accepted literal BASE-leaf equivalence, which is stronger because it needs no positivity. At `k :: Γ`, `genuineCertificate (k :: Γ) C` gives genuine `C.1`. The semantic induction hypothesis, specialized to arbitrary genuine lower `G,H`, their own original support and the same `ν`, proves `BalancedGuardDescent.LowerCorrect Γ C.1 (fun G H d => typedFormula Γ C.1 G H d) ν`. The accepted `actualSourceDescent` then identifies the large disjunct with the conjunction of the requested actual sign and the original all-large condition

`∀ a ∈ (comparisonRow E F).atoms, BalancedRow.threshold (comparisonRow E F) ≤ BalancedRow.input (basisValues k Γ C ν) a.2`.

This condition concerns all original atom occurrences, including later-canceled blocks. Its exhaustive alternative is exactly `BalancedSmallBox.smallBranch k Γ C E F ν`, namely some original complete input below the same original threshold. The proof must establish this all-large/some-small dichotomy rather than assume coverage or enlarge the threshold. With no atoms, all-large is vacuous and smallBranch is false; the original lower-part comparison handles that case.

Both disjuncts are sound: accepted finite-box truth implies the requested actual sign, and accepted large-guard truth implies the same sign. For completeness, all-large and the sign yield the large disjunct. In the some-small case, the accepted original small-input bounds and finite-box completeness yield the first disjunct, using only the genuine certificate and original-support positivity. The accepted finite-box formula retains every correctly signed point of the original box, rather than additionally testing some-small as in the prose at lines 1016–1017; its stronger unconditional soundness makes this harmless, and its small-branch completeness pays precisely the missing case. No semantic lower-comparator premise survives in the final target.

## Three exact targets and proposed proof files

1. `ExactTypedCodeCalibration` / `exact_typed_code_calibration`: literal raw-code equality with this formula's `Formula.encode` on all typed inputs.
2. `OriginalSupportContainment` / `original_support_containment`: emitted-variable containment in the original pair support on all typed inputs, independently of genuineness.
3. `ActualSignSemantics` / `actual_sign_semantics`: actual sign equivalence under genuine source data and positivity only on the original pair support, with no lower-correctness premise.

Proposed candidates, absent during this draft:

- `BalancedTypedCompilerCalibrationProof.lean`: structural exact-code induction using narrow `BalancedRawCompilerCallProof`, `BalancedGuardDescentCodeProof` and `BalancedBoxFormulaCalibrationProof` suppliers.
- `BalancedTypedCompilerSupportProof.lean`: independent structural support induction using narrow `BalancedGuardDescentSemanticProof` and `BalancedBoxFormulaLiteralProof` suppliers.
- `BalancedTypedCompilerSemanticProof.lean`: actual sign induction, internal discharge of `LowerCorrect`, original all-large/some-small exhaustivity and accepted `BalancedBoxFormulaSemanticProof`/`BalancedGuardDescentSemanticProof`.
- `BalancedTypedCompilerProof.lean`: thin exports of the three exact obligations.

Definitions import only the safe accepted definitions through `BalancedRawCompilerDefinitions`; targets add no proof import. Do not import broad `BaseFormulaProof`, old common-layer comparison interfaces or `LinkedResidue`. Candidate files remain absent until root exact review, comparator acceptance and prospective freeze. Only the standard `propext`, `Classical.choice` and `Quot.sound` foundations may occur in accepted axiom closures. The unchanged compiler wrapper, serialized bounded resources, compile-first exact-target checks and actual axiom audit remain required. This drafting step performs no candidate authoring, compiler invocation, accepted-file edit or Git operation.

The exact free-variable equality wrapper, its corresponding all-code constructor, the independently required quantified BASE decision theorem and the Boolean/quantified closure remain PENDING. This component is a calibrated typed comparison-formula supplier, not completion or promotion of the entire paper08 balanced theorem.
