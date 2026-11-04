# Primitive-recursive checked restricted source evaluator

This composition strengthens the upper-bound effectivity justification in paper09 hardness.tex lines 316–319. The targets are the existing ParametricRestrictedSourceEvaluator.evaluate and gammaEvaluate, without changing their definitions or prior semantic calibration.

Joint primitive recursiveness in ((control index, context length),(raw source code, numeric input list)) follows under jointly Primrec H, StrictMono of every section, and identity majorization of every section. Existing PR context replication, source type check, actual default assignmentCode, sparse component environment, optional vector lookup and the accepted PR numeric ordinal evaluator are composed. FixedGammaPrimitive holds for each fixed b, not jointly in b.

The guard still requires input-list length to equal n and the actual source checker to return ground type in the canonical all-ground context. A failed guard returns None. A failed assignmentCode or absent vector coordinate zero also returns None. Successful raw executions do not imply the source fragment, positivity, or omega-free assignment; the accepted typed semantic calibration and totality still require their exact all-ground, Fragment, length, and valuation hypotheses. No malformed-code success is equated with language membership.

This proves primitive recursiveness of the existing Option-valued computation, not a uniform constant number of iterations, a polynomial/runtime bound, joint-in-b control effectivity, unrestricted source semantics, or a source-register/export change. The previous finite successful Scalar interpretation remains unchanged.
