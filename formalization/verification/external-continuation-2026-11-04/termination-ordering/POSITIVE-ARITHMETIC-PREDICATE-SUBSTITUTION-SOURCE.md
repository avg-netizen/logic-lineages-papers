# Binder-aware predicate formula substitution

Source: paper06 arithmetic positive-operator/ID1 discussion. This is a syntactic prerequisite for expressing closure and leastness schemas, not an axiom system or internal derivation.

The input body is the already accepted Positive alpha grammar. The replacement theta is an arbitrary formula in the existing arithmetic-plus-unary-predicate language with free variables alpha+Fin1: left variables are parameters; the final singleton is its argument. Theta may itself contain the predicate interpreted by an arbitrary Q, including negative occurrences. The result is a general formula, with no positivity assertion.

At a predicate atom t, substitutePredicate substitutes the literal embedded arithmetic term t for theta's argument and retains parameter variables. Arithmetic guards are unchanged. Under each body universal binder, liftPredicateFormula moves the old parameters into the old-variable summand, skips the newly bound variable, and retains theta's distinct final argument variable. Thus parameters are not captured. Recursion produces actual existing Formula syntax using allOne, not a semantic oracle.

Targets: lifted replacement realization ignores the fresh body binder exactly; full substitution truth equals interpretation of the original body under predicate x ↦ realize Q theta(parameters,x). The latter uses standard N, all parameter valuations, arbitrary Q, and literal embedded arithmetic term realization. The two predicate interpretations are deliberately distinct.

No ID1 closure/leastness axiom has yet been added, no finite derivation relation or translation to the unrelated paper12 calculus is asserted, and no internal accessibility/ordinal theorem follows. No positivity of the resulting general formula, global WF, original transitivity or register promotion. Proof absent until review/freeze.
