# Balanced comparison with exact original free variables

Subject label: `BalancedExactVariables4`. Source: paper08 `thm:balanced`, in the reviewed window `08-multivariate-collapse-comparison/paper.tex` lines 937–1030. The shared-basis grammar and actual-support convention are at lines 945–959; the theorem's exact same-free-variable clause is at lines 961–966; the signed row and original threshold are at lines 969–982; the cancellation, finite-box and lower-certificate arguments are at lines 989–1026. The inherited positive raw-variable domain is explicit at lines 833–835. Source SHA-256: `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This draft follows the verified `BalancedTypedCompiler3` save `5988f9e575546317d6829cbf4a0a73cd4ce494c8` and changes no accepted supplier.

This component adds a literal tautological wrapper to the accepted actual typed comparison and its accepted raw numeric compiler. Once proved and accepted, its four obligations close the source theorem's **exact same-free-variable comparison-formula** obligation, together with truth and numerical effectiveness. They do not prove the separately required quantified BASE decision theorem, quantified syntax/translation closure or complete balanced theorem. No numbered whole-balanced target is promoted by this draft.

## Original support and literal wrapper

For every actual source shape `Γ`, certificate `C`, and source pair `E,F`, `sourceSupport Γ C E F` is exactly `(rawVariables Γ C E ++ rawVariables Γ C F).dedup`. This is the ORIGINAL pair support, computed before comparison-row cancellation, sign filtering or formula simplification. Deduplication removes repeated raw names only. It does not remove or separate repeated/dependent basis entries, change the common certificate or introduce independent values for shared variables. The accepted raw-variable extraction already implements the source convention that zero outside multiples contribute no support.

`variablesFormula support` is the existing `BalancedBoxFormula.conjunction` applied to the list of existing ordinary `BaseFormula.Formula.equal (.variable i) (.variable i)` formulas, in support-list order. The fold has the existing truth formula as its empty tail. These are actual raw variables in actual BASE terms, not labels interpreted by an independent valuation, new predicate symbols or supplied truth witnesses.

`sourceFormula Γ C E F desired` is the literal existing `Formula.conjunction` of:

1. `BalancedTypedCompiler.typedFormula Γ C E F desired`;
2. `variablesFormula (sourceSupport Γ C E F)`.

The original typed comparison comes FIRST and padding SECOND. No simplifier is applied. Thus every original raw variable remains syntactically present even if all head blocks cancel, the emitted comparison is constant, all relevant branches are empty, or `desired` lies outside `{-1,0,1}`. Each padding equality is true at every natural valuation, including zero, and introduces no variable outside the original support. If the original support is empty, the second conjunct is literal truth and the accepted support containment forces the first conjunct to have no variables.

The first exact target combines two independently stated properties on ALL typed inputs: unchanged truth at every `ν : Nat → Nat`, and, for every index `i`, membership in `sourceFormula.variables` if and only if membership in the original raw-variable concatenation. This is equality of free-variable sets expressed by membership, not equality of list order or multiplicities. In particular each `x=x` mentions its raw name twice, which is harmless. Neither property assumes genuineness or positivity. The forward support direction must use the already accepted `BalancedTypedCompiler.Proof.originalSupportContainment`; the reverse direction is paid by the literal equality padding and `List.mem_dedup`.

## Actual sign semantics

The second exact target quantifies over every shape, typed certificate, typed pair, integer requested sign and original valuation. Its only semantic premises are `genuineCertificate Γ C`, `genuineExpression Γ E`, `genuineExpression Γ F`, and positivity of `ν i` for `i` in `rawVariables Γ C E ++ rawVariables Γ C F`. It concludes the equivalence of the padded formula with `Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = desired`.

This is the actual source semantics at the unchanged original valuation; subtraction is in integers. Outside coordinates may be zero or arbitrary, and empty support requires no positive coordinate. The original positive domain comes from the source level-zero class at lines 833–835 and finite box `[1,L-1]^V` at lines 1015–1018. The wrapper does not add a global positivity assumption or a new semantic lower-comparison premise. Its proof is the truth-preservation result composed with the already accepted `BalancedTypedCompiler.Proof.actualSignSemantics`, retaining exactly those original premises.

## All-shape raw support and literal numeric output

The wrapper's `rawSupport Γ C E F` is exactly `(BalancedEvaluation.codeVariables Γ C E ++ BalancedEvaluation.codeVariables Γ C F).dedup`. It uses the existing extraction algorithm at EVERY shape, including `Γ=[]`. It does not call the positive-shape-only `BalancedBoxFormula.rawSupport`, invent a dummy positive shape, or run an alternative decoder. Existing raw decoder defaults remain unchanged. The accepted all-shape actual-source calibration supplies equality of this support with `sourceSupport` on encoded typed inputs without a genuineness assumption.

`variablesCode support` is `CommonHeadCode.conjoin (support.map (fun i => [(2, 4*i+1, 4*i+1)]))`. The operands `4*i+1` are the EXISTING `BaseTerm.encode` codes of actual raw variable `i`, and tag `2` is the existing equality instruction. The empty tail is the existing true instruction `[(1,0,0)]`; finite conjunction uses the existing postfix tag `6`.

`formulaCode Γ C E F desired` is the literal `CommonHeadCode.conjunction` of the ORIGINAL `BalancedRawCompiler.compileCode Γ C E F desired` FIRST and `variablesCode (rawSupport Γ C E F)` SECOND. The compiler's raw code is preserved as the initial segment, followed by padding and the final conjunction instruction. Its recursion, finite calls, thresholds, original finite boxes, original large guards, ordering, lower certificates, ignored Boolean children and malformed-input defaults are unchanged. No second compiler, reencoding of a chosen formula, new oracle, validity test or input normalization replaces it. `outputCode` merely tuples this expression on the existing `BalancedRawCompiler.Input` type `List Nat × Nat × Nat × Nat × Int`.

The third exact target requires literal equality of `formulaCode` on encoded typed inputs with the existing `Formula.encode` of `sourceFormula`, at every shape and every integer requested sign. It is not only a semantic equivalence or a claim that some code exists. It has no genuineness, positivity or caller-supplied calibration premise. The intended proof combines accepted `BalancedTypedCompiler.Proof.exactTypedCodeCalibration`, all-shape `BalancedBoxEvaluation.Proof.actualSourceCalibration` for both original supports, and the existing finite-conjunction encoding law. Typed actual-source calibration is sufficient; no claim that arbitrary malformed numeric data represents a genuine certificate or has source truth is made.

## Unconditional all-raw computation

The fourth exact target is `Computable outputCode`, on ALL raw tuples, including empty shape, arbitrary certificate and expression codes, and every integer desired sign. This is a constructive computability theorem for the specified wrapper, not a supplied computability premise and not a claim that the entire balanced compiler is primitive recursive.

The original raw compiler already has unconditional computation through `BalancedRawCompiler.Proof.allCodeComputation.2`. The existing all-shape support extractor is already computable via the actual joint evaluator; `BalancedBoxFormula.Program.variables_computable` exposes the exact needed interface on `List Nat × Nat × Nat`. Accepted deduplication, variable-code arithmetic, list mapping and finite conjunction suffice for the added padding. A proof may establish elementary helper programs as primitive recursive, but the full output target remains `Computable` because it includes the original accepted total compiler. No new closed evaluator or oracle is introduced.

## Four exact targets and planned candidates

1. `TruthAndExactVariables` / `truth_and_exact_variables`: unchanged truth at every valuation and exact original variable membership, for all typed inputs.
2. `ActualSignSemantics` / `actual_sign_semantics`: actual source sign under genuine `C,E,F` and positivity only on original pair support.
3. `ExactTypedCodeCalibration` / `exact_typed_code_calibration`: literal equality of the specified raw wrapper with the existing actual formula encoding, for all typed inputs.
4. `AllCodeComputation` / `all_code_computation`: unconditional `Computable` numeric output on all raw inputs.

Planned candidate files, all ABSENT during this draft:

- `BalancedExactVariablesLiteralProof.lean`: truth of literal variable equalities and exact variable membership, using accepted typed support containment.
- `BalancedExactVariablesSemanticProof.lean`: actual sign corollary under precisely the accepted original semantic premises.
- `BalancedExactVariablesCalibrationProof.lean`: exact all-shape support calibration and literal postfix-code calibration.
- `BalancedExactVariablesProgramsProof.lean`: elementary padding program and all-raw computability by composition with the unchanged original compiler.
- `BalancedExactVariablesProof.lean`: thin import/export aggregation for the four obligations.

Definitions import only accepted definitions through `BalancedTypedCompilerDefinitions`; targets add `Mathlib.Computability.Partrec` and no proof import. Candidate imports should remain narrow, using the named accepted suppliers. Do not import broad `BaseFormulaProof`, old common-layer comparison interfaces or `LinkedResidue`. Only the usual `propext`, `Classical.choice` and `Quot.sound` foundations may occur in accepted axiom closures.

This is a draft for parent/root exact-scope review. No comparison gate or prospective freeze has yet been run. Candidates must remain absent until root approval, comparator acceptance and prospective freeze. This step performs no candidate authoring, compiler invocation, accepted/frozen-file edit or Git operation. The separately required quantified BASE decision supplier and Boolean/quantified theorem closure remain PENDING.
