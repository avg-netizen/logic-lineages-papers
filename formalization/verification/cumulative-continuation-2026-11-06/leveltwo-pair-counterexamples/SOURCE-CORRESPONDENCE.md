# Closed pair counterexamples

This component implements the finite existential translation step of paper08,
`thm:leveltwo`, lines 815–824, for two already valid polynomial expressions.
It reuses the full polynomial graph theorem; it does not decide the emitted
sentence or establish the whole level-two source theorem.

The package records a computed finite degree, the original arity n, one exact
natural existential prefix, literal word-linear graph equations, the difference
of the two child output nodes, a comparison mode, and a closed-coordinate flag.
The graph is the existing graph of `add a b`: its auxiliary sum node is harmless
bookkeeping, and only a and b's child values are compared. Both use the same
valuation. Original indices below n are positive; all auxiliary nodes range
over all naturals. Every used name is bound by the emitted finite prefix.

The failed scalar tests are a-b > 0 for weak comparison, a-b >= 0 for strict,
and a-b != 0 for equality. A false closed-positive-coordinate flag also makes
the full relation fail. Exact source-coordinate computation of that flag and
the original canonical source adapter are later interfaces, not assumptions
silently discharged by this component.

The all-raw numeric compiler is primitive recursive and calibrated to the
literal package. Validity and freshness occur only in its semantic theorem;
no source correctness is claimed for invalid codes or out-of-range names.

The initial draft comparator had an implication/iff precedence error. It was
rejected before acceptance and is preserved with its freeze. Explicit
parentheses corrected the parse to the documented conditional equivalence;
the corrected comparator was frozen before the successful native proof check.
No accepted source statement was changed. Register remains 167/2/20 of 189.
