# Independent original depth syntax refactor review

Read preserved failed original, actual full diff, generic helper and exact caller application. All six original theorem headers unchanged; only observationsSubst body and helper import change. Other five proof bodies preserved. No original observations/induction/target AST changed.

Generic schema retains ordered five observations: Code guard, opaque accepted formula, bounds, pair decomposition of bound, depth. Actual caller supplies exactly original CodeValidityGuard.check n, OriginalCodeBoundsRecursion.bounds n, OriginalEnumerationDepth.depth n and InternalPairing.pairing. Formula substitution equality is discharged by existing actual acceptedSubst, not assumed as a new public premise. Generic proof uses original program substitution and numeral/vector syntax.

Approved exact pins for native checking under unchanged limits. Not native success, memory guarantee, endpoint acceptance or a substantive result. Original failed source/log preserved.
