# R006 finite internal proof block

This current-round candidate proves the seven already-preflighted exact
syntax/internal-calculus targets. It does not prove paper06 `lem:id1`.
The current whole source target remains
`ContextUniformTargets.ActualContextUniformInternalAccessibility`.

`monotonicityTree` recursively constructs a finite derivation for every
positive formula. Arithmetic leaves reuse their assumption; predicate leaves
instantiate the pointwise universal implication. Conjunction and guarded
implication use the corresponding introduction/elimination rules. The
universal case retains the eigenvariable condition by mapping the complete
hypothesis context through `weaken`; its pointwise hypothesis and source
universal formula are transported with literal checked syntax identities.

For reverse unfolding, write `F` for the one fixed positive body and use
`F(I)` itself as the leastness invariant. Closure gives `F(I) -> I`.
Monotonicity therefore gives `F(F(I)) -> F(I)` as a finite derivation.
The already accepted invariant-induction derivation yields `I -> F(I)`.
Parameters remain first-order variables of the invariant, and no second
inductive predicate or varying operator is introduced. The source-body
instance simply applies this generic proof to the literal existing tagged
source operator.

No proof constructor accepts model truth, accessibility, computability,
standard-natural least-set membership, or an arbitrary source theorem.
The four auxiliary equalities compare native first-order syntax, not
standard-model realizations. All proof trees use the frozen accepted
`InternalCalculus.Derivation` rules.

These are prerequisites for genuine internal source induction. Internal
PA proofs of the arithmetic graph/code/substitution facts, the same-Gamma
encoded computability formulas, J and typed neutral/lambda/constructor
derivations, and the full computable-substitution fundamental derivation
remain unpaid. No new round is started under the user-requested pause.
