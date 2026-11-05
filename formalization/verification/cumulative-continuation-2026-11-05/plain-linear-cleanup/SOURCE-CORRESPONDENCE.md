# Remove actual linear names before nonlinear branching

The program selects original occurrence names which satisfy the existing exact
linearity test, preserving repetitions, and applies the actual checked linear
block elimination. The target preserves existential satisfiability and exactly
the finite nonlinear-name set. Every surviving name must occur nonlinearly, and
an empty nonlinear-name set must leave a literal constant formula after cleanup.
Plain syntax, literal encoding and primitive-recursive implementation are retained.

The existential valuation proposition is only the original semantic contract,
not an oracle used by the program. This component prepares exhaustive maximal-
name selection and the decreasing-frontier argument; it does not yet claim a
multiple-name decision procedure or arbitrary alternating quantifier elimination.
