# Paper 16 realization closure with the structural lambda theorem

Continuation date: 2026-11-22 (America/Chicago).
Base: `9a8fd8f8ffd9c1ab27b91096dc1e52aa196bb413`.

## Exact printed clauses

Paper 16 `sections/ordinals.tex:423-448` defines realization over finite semantic
types, with countable ordinals at the base and all set functions at arrows.
`lem:realization` asserts strict-predecessor closure, semantic downward closure,
closure under nonempty countable pointwise suprema, and the typed lambda
fundamental lemma. Its proof also describes transport along finite beta chains.

The old `NativeRealizationClosure` supplies the first three clauses (and the
semantic shape and pointwise-supremum existence infrastructure). The old
`NativeRealizationFiniteChains` supplies transport through finite nonempty strict
chains; a zero-step transport is immediate identity. The former lambda rule
assumed realization of each substituted body and was insufficient for the full
structural assertion.

The new `TypedLambdaRealization.FullTypedLambdaFragment` supplies native typing,
literal substitution, the structural fundamental theorem, and its closed pure
lambda corollary. Its grammar has all four constructors of the typed lambda
fragment: variables, interpreted constants, application, and abstraction. Its
compiler uses the existing native application/lambda/bound constructors, and
its denotation uses the existing unrestricted function spaces. The lambda case
derives body realization by induction under an extended realizing environment.
There is no assumed body-realization or compiler-correctness supplier.

## Source scope of the structural clause

The fragment uses exactly the finite semantic types and their homomorphic
translation introduced at `ordinals.tex:390-392`. A constant interpretation
must realize its assigned semantic value, and the free environment must realize
its valuation; these are the usual interpretation hypotheses of a fundamental
lemma, not extra mathematical assumptions replacing its conclusion. Arbitrary
closed native subterms can be interpreted constants. The source's separately
realized arithmetic terms and tower operators use this arrangement at
`ordinals.tex:499-550`.

The assertion is not a denotation theorem for every raw `Spine.Expr`, marked
auxiliary syntax, or arbitrary native T constant at an untranslated actual
ground type. The printed clause does not state that broader theorem. No source
sentence is deleted or weakened. The independent review in this checkpoint's
`ordinal-frontier` directory checks this interpretation against the manuscript.

## Frozen conjunction

New target:
`LogicLineages.PersistentMarking.NativeRealizationComplete.FullRealization`.
Its defining file is
`LogicLineages/NativeModule/PersistentMarking/NativeRealizationCompleteTargets.lean`.
It conjoins the actual old closure target, the new full structural-fragment
target, and the actual old finite-chain target. These use the same closed-native
term structure and confined relation. Their well-foundedness proofs are
propositional witnesses of that same relation, not different chosen ranks.

The intended exact alias is `NativeRealizationComplete.exact_FullRealization`,
typed against this frozen conjunction. It introduces no theorem premise and
will be assembled from the checked component endpoints. This file and the
target are hashed before the new proof is written. Native success and the
completed source comparison are required before numbered adoption.
