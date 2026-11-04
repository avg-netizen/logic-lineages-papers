# Exact finite-pair actual collapse equation

Target-only proposal, not an effectivity certificate.

Paper09 hardness.tex lines316–319 invokes finite heads and effective collapse for the upper bound. Paper05 foundations.tex cor:finite-head (existing ActualFiniteHeadTargets correspondence lines265–277) supplies the finite-head setting. This component concerns the separate generic-control actual collapseWith, not a changed original collapse.

The represented ordinal is ordinary omega*a+b, including a=0 and b=0. The actual norm is exactly 2*a+b. ExactRepresentation includes injectivity and representation of every strict ordinal predecessor by a lexicographically smaller natural pair. ExactPredecessors identifies the actual norm-bounded set with the explicit rectangle 0≤q≤a and 0≤r≤G(2*a+b), filtered by lexicographic decrease and 2*q+r≤G(2*a+b). No predecessor is discarded by a sufficient-budget hypothesis.

ExactMaximum retains the original maximum recursion, with empty maximum zero. It is an equality to the actual collapseWith values, not a new oracle or assumed recurrence. G is any Nat→Nat; monotonicity, majorization and computability are not premises.

This does not yet define a terminating executable evaluator, prove primitive recursiveness/computability of the value, source upper bound, completeness, runtime, or publication. The ordinal expression used by generic source collapse involves natural operations; its further calibration to this ordinary finite pair is separate if needed.
