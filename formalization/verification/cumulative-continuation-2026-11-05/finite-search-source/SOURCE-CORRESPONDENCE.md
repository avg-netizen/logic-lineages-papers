# Exact composition of finite search and scoped additive decision

This fragment takes Boolean and literal finite-bounded closure of the checked
ScopedPhiParameters source fragment. Every recursive call receives the actual
current finite valuation table; bounded search performs the exact original-name
update before deciding an inner unbounded additive block. No outer environment
is frozen across that update. Original binders, shadowing and Boolean positions
are preserved.

The six semantic targets prove inclusion of both existing fragments, actual
source truth/domain, exact active-environment search, a mixed bounded nonlinear
outer/unbounded additive inner family, and a literal rejected unbounded nonlinear
family. This is an exact compositional restricted decision, not unrestricted
nonlinear quantifier elimination or full BASE. Numeric effectivity is separate.
