# Balanced raw recursive BASE-code constructor

Subject label: `BalancedRawCompiler3`. Source: paper08 `thm:balanced`, especially `08-multivariate-collapse-comparison/paper.tex` lines 1007–1026. The actual shared-basis grammar is at lines 945–959, the signed row at lines 969–974 and the original threshold `eq:balanced-L` at lines 980–982. Source SHA-256: `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`. This draft follows the accepted `BalancedGuardDescent5` checkpoint `b4045a0b` without changing that supplier or another accepted file.

This is a bounded raw CODE-construction supplier. It defines the actual structurally recursive numerical constructor, combines the accepted original finite box and translated original large guard, establishes exact calls with strict actual-shape descent, and requires unconditional computability of the concrete constructor. A typed recursive `BaseFormula.Formula`, its positive-level literal code calibration, its actual-source semantic induction and its original-support induction remain PENDING. This supplier does not prove the whole balanced comparison theorem, exact same-free-variable language, Boolean/quantified decision, or the quantified BASE decision theorem.

## Empty actual shape

At shape `[]`, balanced syntax is the existing `CommonLayerSyntax.BaseTerm`. `baseCode` emits the existing postfix equality instruction `(2,E,F)` for desired sign zero, the strict-order instruction `(3,E,F)` for minus one, reversed strict order `(3,F,E)` for one, and the falsity instruction `(0,0,0)` for every other integer. These are exactly the literal choices used by `CommonLayerProgram.baseCode`; the short definition is reproduced here to avoid an unrelated common-layer import closure. It neither evaluates the terms nor supplies a new arithmetic predicate.

The sole typed object defined here is `baseFormula`, the corresponding literal leaf formula on two actual BaseTerms. `ExactFiniteCallEquation` requires that compiling their actual term encodings at shape `[]` gives exactly this formula's existing encoding and that its truth under every raw valuation is the requested integer sign of the two actual natural values. No positivity, source-validity, certificate or sign-range premise is needed at this leaf. Any raw certificate code is ignored at the empty shape. This is not an all-raw decode/encode roundtrip claim and is not positive-level source calibration.

## Structural raw recursion and exact branch order

The complete raw input is `(shape, certificateCode, leftCode, rightCode, desired)` of type `List Nat × Nat × Nat × Nat × Int`, exactly the accepted guard-descent call type. `compileCode` is defined by structural recursion on the actual `List Nat` shape. It is not defined by a finite-graph result, by an arbitrary supplied lower comparator or by an asserted recursion equation.

At caller shape `k :: Γ`, the literal output is:

1. `BalancedBoxFormula.formulaCode k Γ C E F desired`;
2. `BalancedGuardDescent.sourceAssemble k E F desired` applied to the ordered list of recursively computed child results;
3. the existing postfix disjunction instruction joining these two codes.

Thus the exact order is finite-box code first, translated-large code second, then `(7,0,0)`. `CommonHeadCode.disjunction` performs precisely that concatenation. No runtime evaluator instruction, alternative Boolean encoding, guard simplification, small-input test, enlarged threshold or new finite enumeration is introduced. The finite-box constructor remains the accepted original-support/original-threshold construction, which retains all correctly signed points of that finite box. Its accepted soundness and small-branch completeness are the intended later semantic suppliers.

The lower calls are exactly `BalancedGuardDescent.sourceChildren k Γ C E F desired`, in their original order and with repeated occurrences. The recursive invocation passes each child's certificate, left term code, right term code and desired sign unchanged. Its first argument is the structurally smaller `Γ`. The target proves that each actual child tuple's shape is precisely `Γ`, rather than merely another shape of equal or smaller length. This equality makes the eventual finite-call equation about the child's actual full tuple, not a substituted query.

Every child retains `BalancedSourceAdapter.lowerCertificate C`. On actual encoded certificates, the already accepted source adapter and guard-descent calibration identify this with the original `C.1`; this component does not replace that certificate, recompute a separate certificate per guard or introduce an independently valued basis. The original complete-input/lower-part term codes, actual balanced numeral defaults and requested signs stay in the accepted children unchanged. Original Boolean instructions still have their accepted harmless zero-versus-zero equality children; those results are computed and then ignored by assembly.

All raw source codes, malformed-code defaults, shapes, integer signs and result lists remain in the domain. In particular, `assemble` on arbitrary result lists keeps the existing `sourceAssemble` zip/truncation behavior. No claim says that unrelated truncated result lists correspond to the constructor. The exact recursion equation uses the full ordered map of actual recursive child results, with one result per original guard instruction.

## Finite calls and unconditional effectivity

`children` is empty exactly at the empty shape and is the accepted `sourceChildren` at an upper shape. The target requires its length to be the original adapter guard-code length and every child's actual shape and certificate to be the values just described. The measure is exactly `shape.length`; every actual child strictly decreases it, including Boolean children and malformed raw inputs.

`recursiveCode` simply applies the structurally defined `compileCode` to the five components of its complete input. The exact equation is `recursiveCode a = assemble a ((children a).map recursiveCode)`. It must be proved for all raw inputs, not supplied as a premise. The child-shape equality is necessary to derive it from the structural definition.

`NumericalInterfaces` requires concrete, unconditional `Computable` witnesses for the base constructor, full `children`, full `assemble` and actual measure. Accepted guard-descent primitive-recursive maps supply the lower-call list and large-result substitution. Accepted `BalancedBoxFormula` all-code computation supplies the finite-box constructor. The existing literal disjunction constructor supplies the final Boolean combination. There is no lower-comparator assumption, validity oracle, successor-head oracle, certificate-correctness hypothesis or incoming effectiveness witness.

`AllCodeComputation` requires the unchanged `FiniteGraph.graph` at depth `measure a + 1` to return exactly the singleton `[(a, recursiveCode a)]` and concludes unconditional `Computable recursiveCode`. It can use the accepted thin `BalancedBoxEvaluationGraphProof` theorem `BalancedBoxEvaluation.Graph.exactDecreasingGraph`, instantiated with the concrete numerical interfaces and derived finite-call equation. This is constructive finite-depth computation of the specific raw constructor, not mere existence of a semantically equivalent output.

No `Primrec` claim is made for the entire compiler: the finite-box constructor already uses the accepted general computable evaluator. No computability result here is conditional on positive-level semantic calibration. Conversely, raw computability and strict descent do not discharge that calibration or the lower semantic/support premises from `BalancedGuardDescent`.

## Three exact targets and proposed proof files

1. `ExactFiniteCallEquation` / `exact_finite_call_equation`: raw empty case, literal actual BaseTerm leaf encoding/sign semantics, exact upper child count/shape/certificate, strict measure descent and actual full-query finite-call equation.
2. `NumericalInterfaces` / `numerical_interfaces`: unconditional concrete base/children/assembly/measure programs on all raw inputs.
3. `AllCodeComputation` / `all_code_computation`: exact unchanged finite graph output and unconditional computability of the structurally defined raw compiler.

Proposed candidates, absent during this draft:

- `BalancedRawCompilerCallProof.lean`: local leaf encoding/sign facts, raw child shape/certificate laws and finite-call equation. The accepted narrow `BalancedGuardDescentCodeProof` may supply child count/descent facts; `CommonLayerProgramProof` is also a permitted narrow supplier if its leaf encoding theorem is useful. Short local Boolean encoding facts avoid a broad runtime proof import.
- `BalancedRawCompilerProgramsProof.lean`: explicit concrete programs using `BalancedGuardDescentProgramsProof`, `BalancedBoxFormulaProgramsProof` and `CommonHeadCodePrimitiveProof`.
- `BalancedRawCompilerProof.lean`: the three exact exports and finite-graph instantiation using `BalancedBoxEvaluationGraphProof`.

Do not import broad `CommonLayerProgramDataProof`, `FiniteGraphProof`, `ComparisonAssemblyListProof`, `BaseFormulaProof` or `LinkedResidue` to prove this bounded result. In particular, reproduce the short elementary base-code program locally instead of importing `CommonLayerProgramDataProof`. Candidate files remain absent until exact review, comparator acceptance and prospective freeze. The immutable compiler wrapper, serialized resource limits, exact target checks and actual axiom-closure audit remain mandatory. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. This drafting step performs no candidate authoring, compiler invocation, accepted-file edit or Git publication.
