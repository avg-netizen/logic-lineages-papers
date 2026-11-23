# Structural realization for the full typed lambda/application fragment

Reviewed base: `9a8fd8f8ffd9c1ab27b91096dc1e52aa196bb413`.

## Printed claim and existing boundary

Paper 16 `16-persistent-marking-termination-ordering/sections/ordinals.tex:423–448` defines realization at the finite semantic types and states the typed lambda fundamental lemma. Arrow values are all set functions, and the proof uses strict beta reduction of application to the substituted body. The following sentence extends transport to finite beta sequences.

The accepted `NativeOrdinalRealizationTargets.NativeLambdaRealization` gives the abstraction rule with realization of every substituted body as a premise. `NativeLambdaChainTargets.NativeLambdaChainRealization` extends it through finite strict chains and explicitly says it is not a structural fundamental lemma over all typed native terms. Neither derives body realization by induction on a typed expression.

The new target derives that induction for the complete simply typed lambda/application grammar over the existing `FiniteType` hierarchy. It permits arbitrary nesting of lambdas, arbitrary typed de Bruijn variables, and arbitrary closed native constants whose interpretations are already realized. No monotonicity or restricted function-space interpretation is introduced.

## Exact grammar and native correspondence

New namespace: `LogicLineages.PersistentMarking.TypedLambdaRealization`.

| Grammar constructor | Semantic operation | Exact native compilation |
|---|---|---|
| Typed variable | Lookup in the semantic environment | Lookup of its actual closed native term, or the existing `.bound (nativeType A) i` under local binders |
| Constant | The supplied constant value | The supplied closed native realizer's literal `Expr` value |
| Application | Ordinary application in `Value (.arrow A D) = Value A → Value D` | Existing `NativeReduction.app (nativeType A) (nativeType D)`; original application head and argument order |
| Lambda | Set-function abstraction with extended semantic environment | Existing `Spine.Expr.lam (nativeType A)`; local bound indices shift once, and closed native entries remain literally unchanged |

`nativeType A` abbreviates `actualType (nativeShape A)`. In particular semantic base `ι` maps to actual `σ = o → o`, exactly as in `NativeOrdinalRealizationTargets`. The theorem concerns realizer-typed lambda syntax. It is not an interpretation theorem for every raw `Spine.Expr`, every original T constant at arbitrary actual types, or marked auxiliary terms. Arbitrary closed native subterms may serve as constants, but their semantic realization remains the usual explicit constant-interpretation premise.

There is no assumed lambda-body theorem, compiler supplier, or semantic equation oracle. The compiler is a structural definition over all four grammar constructors. Its native typing and exact substitution bridge are obligations, followed by the structural realization theorem.

## Frozen obligations

New files under `formalization/LogicLineages/NativeModule/PersistentMarking/`:

- `TypedLambdaRealizationDefinitions.lean`: intrinsic syntax, full set-function evaluation, literal compiler, explicit bound/closed entry environments, and the one-binder entry substitution relation.
- `TypedLambdaRealizationTargets.lean`: the frozen propositions below.
- `TypedLambdaRealizationSyntaxProof.lean`: planned native typing and exact substitution proof.
- `TypedLambdaRealizationProof.lean`: planned structural realization and pure closed corollary.

1. `NativeCompilation`: every typed grammar expression compiles to `NativeIn` in each binder context fitting its entries. This is the existing native typing/ordinary/free-name-closed/native predicate, not a replacement language semantics.
2. `LiteralSubstitution`: the compiler commutes exactly with the existing `Spine.substitute (.cons u.val .nil) depth`, whenever entry environments are related by the explicit one-binder substitution relation. The relation's cases retain lower bound indices, replace the selected bound index by the actual closed argument, decrement higher indices, and preserve closed terms.
3. `StructuralFundamental`: for realizing constants and a realizing closed variable environment, the literal compiled term realizes its ordinary denotation. The lambda case is to follow from the body induction hypothesis and exact substitution, using the accepted strict beta abstraction rule.
4. `PureClosedFundamental`: the empty-constant, empty-free-context specialization has no realization premise at all and covers every closed pure typed lambda/application term.
5. `FullTypedLambdaFragment`: their conjunction, explicitly scoped to this grammar.

## Reused exact interfaces

- `NativeOrdinalRealizationTargets.lean`: existing finite semantic types, native term structure, and abstraction-rule statement.
- `NativeOrdinalRealizationProof.lean`: `exact_NativeLambdaRealization` and the checked strict-beta route.
- `NativeTowerSyntaxProof.lean`: the public `NativeIn`, `closedIn`, `close`, `boundIn`, `appIn`, `lamIn`, and `unchanged` interfaces.
- `ClosedSyntaxProof.lean`: shifting/substituting an actual empty-context typed closed term leaves it unchanged.
- `SpineSyntax.lean`: the actual de Bruijn `shift` and `substitute` operations.

These files are used unchanged. No manuscript, accepted proof, register, pin, or native checker is changed. Native proof validation belongs to the root's serialized gate. Numbered `lem:realization` promotion requires a separate owner decision about the printed clause's exact coverage; this packet does not silently replace it by a weaker theorem or promote it.

## Preproof freeze

Definitions, targets, and this source map are written and SHA-256 recorded in `LEDGER.md` before either new proof file is created. Actual freeze timestamps are UTC; the checkpoint date follows the user-facing America/Chicago date.
