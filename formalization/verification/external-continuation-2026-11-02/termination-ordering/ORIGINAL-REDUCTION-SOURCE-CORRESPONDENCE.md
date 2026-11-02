# Every original T reduction, context and substitution instance

Source paper06 unlabelled corollary-15, lines522–525. Uses the existing `Source.RootReduction` with exactly beta, case-zero, case-successor, recursor-zero and recursor-successor constructors, and existing `Source.Reduction` closure in both application positions, lambdas and each ranked argument. No new reduction or ordering relation is introduced in Definitions.

`RootOrientation` and `ContextualOrientation` assemble the actual existing confined orientations and literal context closure. They keep arbitrary ordinary source terms, scope and type. The ranked clause retains the original condition that all other argument positions coincide.

`RootSubstitutionClosure` and `ContextualSubstitutionClosure` prove actual syntactic preservation of these exact reduction relations under any typed ordinary `Substitution`. In particular the beta case must prove the real single-substitution/lift composition equation, not replace its contractum by a definitionally convenient semantic application. Binder lifting and variable substitutions remain capture-avoiding. These statements are not arbitrary Weak/Strict substitution stability.

`SubstitutedContextualOrientation` then concludes the original confined strict comparison on both actual substituted endpoints. It pays the explicit substitution-instance clause without an assumed strong-pair or monotonicity oracle. All typeSupport conclusions come from orienting the actual instantiated source reductions; no ambient context support is added. Only the complete five-target dependency chain pays the full corollary; stability and well-foundedness remain separate.
