# Independent typed-lambda source review

Client date: 2026-11-22 (America/Chicago). Reviewed base:
`9a8fd8f8ffd9c1ab27b91096dc1e52aa196bb413`.

## Verdict

**No material statement-to-source finding for the printed finite-semantic-type
lambda/application fragment.** The new `StructuralFundamental` is a genuine
structural fundamental lemma with a defined denotation, all four syntax cases,
and the literal native term as its output. It closes the earlier missing lambda
clause when combined with the accepted native realization closure results.
The separate finite-chain theorem supplies the last sentence of the printed
proof. No weaker manuscript rewrite is needed for this conclusion.

The standard interpretation hypotheses are explicit: the constants and the
closed substitution for free variables realize their assigned values. The
realization of an arbitrary lambda body is no longer an input. It follows from
the structural theorem for that body with an extended realizing environment.

This verdict does not claim a denotational semantics for every raw native
`Spine.Expr` or every original system-T term at every actual type. The printed
realization relation is defined at the semantic finite types whose base is
countable ordinals and whose actual base is `o → o`. Its ordinary typed lambda
fragment is exactly the subject of the new theorem. A purported all-actual-type
fundamental theorem would require a different semantic statement and remains
unsupported by this packet.

## Source setting and exact coverage

Paper 16 `sections/ordinals.tex:390–392` introduces semantic base `ι`, countable
ordinal values, actual type `σ = o → o`, and homomorphic translation of arrows.
Lines 423–432 use all set functions at arrows and define realization on closed
actual terms at those translated types. The printed lambda sentence is at
lines 438–439, inside this semantic setting. The proof at lines 446–449 uses
ordinary strict beta reduction and backward realization transport.

The new definitions retain that setting without a new ordinal interpretation:

| Printed ingredient | Exact Lean source | Assessment |
|---|---|---|
| Finite semantic types with ordinal base and full function arrows | `OrdinalRealizationTargets.lean:9–17`; `TypedLambdaRealizationDefinitions.lean:12,79–86` | `evaluate` uses the existing full `Value` hierarchy. No monotonicity restriction or smaller arrow domain appears. |
| Actual translation `ι ↦ o → o`, arrows homomorphically | `NativeOrdinalRealizationTargets.lean:12–25`; `TypedLambdaRealizationDefinitions.lean:12` | Uses the established `nativeShape` and `actualType`, and the actual `ClosedNativeTerm` carrier. |
| Typed variables and arbitrary nesting of application/abstraction | `TypedLambdaRealizationDefinitions.lean:14–25` | `Var` and `Term` cover each standard typing rule; contexts admit repeated types, unused entries and arbitrary finite depth. |
| Realized constants and realizing substitutions for free variables | `TypedLambdaRealizationTargets.lean:31–40` | Universally quantified constant interpretations and environments, with the ordinary logical-relation hypotheses. No lambda-body premise. |
| Ordinary application and lambda syntax | `TypedLambdaRealizationDefinitions.lean:68–77` | Compiles literally to `NativeReduction.app` and `Spine.Expr.lam`, with no normalization, selected representative or auxiliary head. |
| Actual typing and closed-native membership of the result | `TypedLambdaRealizationTargets.lean:13–17,38–40`; `NativeTowerSyntaxProof.lean:19–30` | `NativeCompilation` proves existing typing, validity, ordinary syntax, free-name closure and native-head membership. At the empty binder context it gives the original closed native carrier. |
| Capture-avoiding substitution below nested binders | `TypedLambdaRealizationDefinitions.lean:95–107`; `TypedLambdaRealizationTargets.lean:21–26` | Equality uses the existing `Spine.substitute`, at arbitrary depth, with the actual closed argument inserted. It is a proved compiler property, not an assumed supplier. |
| Denotation preservation for the compiled expression | `TypedLambdaRealizationTargets.lean:31–40` | The output term's `val` is exactly the literal compilation, and it realizes `evaluate cv t η`. |
| Closed pure lambda terms | `TypedLambdaRealizationTargets.lean:44–49` | All closed pure typed terms are included with neither constant nor environment realization premises. |

All listed new filenames are under
`LogicLineages/NativeModule/PersistentMarking/`. The generic
`OrdinalRealizationTargets.lean` is under `LogicLineages/PersistentMarking/`.

## Why no reverse raw-syntax coverage theorem is missing here

The semantic lambda language is presented directly by its complete four
constructors: variable, interpreted constant, application and abstraction.
The native typing and exact substitution theorems connect that entire grammar
to the repository's existing source syntax. This is not a predicate selecting
only already-realizing terms, a bounded family of examples, or an unproved
compiler interface. Every term of every finite semantic type and finite context
is quantified in `StructuralFundamental`.

The manuscript expressly permits a typed de Bruijn representation for ordinary
terms (`sections/foundations.tex:23–30`). Thus intrinsic de Bruijn typing is a
representation of the stated variable/application/lambda typing rules. A
second parser or inverse compiler from an independently defined semantic
lambda AST is not needed: the paper has no competing semantic lambda AST whose
inhabitants must first be shown to enter the new grammar.

The whole native system-T grammar is larger. In particular, actual ground `o`
is not the translation of any semantic `FiniteType`. Native expressions can
contain binders at `o`, such as the printed `Z = λz:o.z` at
`ordinals.tex:499`, while a pure semantic-base lambda term has no such binder.
This does not remove `Z` from the realization argument: `Z` is independently
shown to realize zero and may then be inserted literally as a realized constant
of semantic base type. The same distinction applies to the iterator's native
recursor and ground binders (`ordinals.tex:452–457`). Its separate realization
theorem supplies the constant interpretation used in subsequent lambda terms.

This is also how the paper actually uses the fundamental lemma. The displayed
add/mul/pow/fix expressions at `ordinals.tex:513–525` form lambda/application
terms over already assigned ordinal-realizer types. The extractors at
lines 532–551 prefix translated-type lambdas and apply realized `It`, `fix` and
`Z`; the internal native terms are closed constant entries. The new grammar
covers these lambda skeletons, while the required realization of each chosen
constant remains the separate mathematical obligation stated by the theorem.
No claim that the new theorem alone proves all arithmetic or calibration
suppliers follows from this review.

## Assumptions, ranks and the previous obstruction

`StructuralFundamental` has the quantifier order
`∀ S, ∃ wf, ∀ C ct cv, constantsRealize → ∀ Γ A t ρ η,
environmentRealizes → ...`. The rank well-foundedness witness is returned
before any constants, term, or environments are selected. It is not an external
accessibility assumption, and it cannot depend on the term being interpreted.
All rank references are through the existing `Realizes (nativeTerms S) wf`.
Proof irrelevance for `WellFounded` makes this the same rank interpretation as
the existing closure and finite-chain endpoints, even though separate
conjuncts expose separate existential well-foundedness witnesses.

The constant hypothesis does not assert that every semantic function has a
native realizer. It says that any supplied native constants realize the
particular values used to interpret them. This is exactly the needed premise
for a logical-relations theorem over a language with interpreted constants.
Likewise, the environment hypothesis is the usual closing-substitution
condition, not a theorem about the term being proved. The pure closed
specialization confirms that neither premise is retained when there are no
constants or free variables.

The earlier independent review
`verification/github-round2-review-2026-11-22/P16-SOURCE-REVIEW.md:150–195`
identified the missing denotation and structural theorem; the old abstraction
rule (`NativeOrdinalRealizationTargets.lean:35–44`) assumed realization of all
substituted bodies. Those omissions are repaired by `evaluate`, the complete
grammar, the exact compilation/substitution obligations, and
`StructuralFundamental`. The broader all-original-T interpretation discussed
in the old Opus correspondence remains a different, unspecified semantic
claim; it is not the meaning adopted for the source's finite-semantic-type
lambda fragment here.

## Complete numbered-lemma composition

The appropriate complete statement consists of:

1. `NativeOrdinalRealizationTargets.NativeRealizationClosure`, for strict
   backward transport, semantic downward closure, and nonempty countable
   pointwise suprema, including existence of the supremum.
2. `TypedLambdaRealization.FullTypedLambdaFragment`, for the structural
   fundamental lemma and its proved native syntax/substitution correspondence.
3. `NativeRealizationChain.NativeRealizationFiniteChains`, for every finite
   nonempty strict chain. The zero-step case is the unchanged realization
   hypothesis.

This is the root's planned `NativeRealizationComplete` assembly. Numbered
adoption is justified once its frozen conjunction has its own successful
native exact/axiom gate. The source comparison itself has no remaining
lambda-fragment coverage blocker.

The historical wording risk in “strict predecessor” remains as recorded in the
earlier review: the Lean relation transports realization from the smaller
target backward to the larger source. That is the direction explicitly used
in the printed proof at `ordinals.tex:447–449` and in the rank-realization
definition. This packet does not claim the opposite rank-decreasing transport.

## Native evidence and immutable source pins

The definitions and targets passed unchanged in
`build-reports/1795411144544945494-11.json`. Their source map and hashes were
frozen at `2026-11-23T05:17:23.157575+00:00`, before the proof modules existed,
as recorded in the realization lane's `LEDGER.md`.

Actual native gate03, `build-reports/1795411295477093868-11.json`, passed both
proof modules. Its entries give return code 0, 1.426 seconds and 924,480 KiB
peak RSS for the syntax proof, and 1.023 seconds and 951,140 KiB for the
semantic proof. The named module logs show:

- `nativeCompilation`, `closedCompilation`, `literalSubstitution` and
  `closeUnderBinder`: exactly `[propext, Quot.sound]`.
- `structuralFundamental`, `pureClosedFundamental` and
  `fullTypedLambdaFragment`: exactly
  `[propext, Classical.choice, Quot.sound]`.

The declaration namespace is
`LogicLineages.PersistentMarking.TypedLambdaRealization`; the compiled import
paths are under `LogicLineages.NativeModule.PersistentMarking`. The failed
first syntax-proof draft is retained in the realization lane; the accepted
syntax repair changed no frozen definition, target or source map.

| Reviewed file | SHA-256 |
|---|---|
| `TypedLambdaRealizationDefinitions.lean` | `b535593ef9e4fde29674aaa35842f58dc71525e4b105049732b6e4992fde8f94` |
| `TypedLambdaRealizationTargets.lean` | `6403883e03cef129bc1250dbcbbd7962cc4c216248bfb0fab5722856d123290b` |
| `TypedLambdaRealizationSyntaxProof.lean` | `5320c3324008b7fef92d771e28f49fc95d6117de370ff48b6a275061541db8a8` |
| `TypedLambdaRealizationProof.lean` | `c0cf01b6b83d1af0acd7ac8143004cf1e88befd0edcd19e1e28d652cee5cb22e` |
| `realization/SOURCE-MAP.md` | `2ce4c550b20c695bd6b6ecaccadc3de8ea7334cb6c2555f603d00693f808db7f` |
| `NativeOrdinalRealizationTargets.lean` | `8d4b8e69d8ef4a4ee83110a2500b10a11467791238b65938bd81765cdce9dad3` |
| `NativeRealizationChainTargets.lean` | `5a04283bd9360300fe1ea6a8a72157827122b5b0618fc7db2580df565ca1312d` |
| Paper 16 `sections/ordinals.tex` | `526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5` |
| Paper 16 `sections/foundations.tex` | `a1f3a425ac6b92ecd4beceab77f271a1b9af97343360a9eee304beb23c7537e0` |

This independent review concerns definitions, quantifiers, source scope and
recorded native evidence. It does not duplicate proof-body review, run a
compiler, edit the realization packet, modify the register or assert the
root's final assembly gate has already passed.
