# Supporting merely computable recursion

Not a numbered manuscript promotion. The need comes from current18's fixed
arbitrary computable admissible policy and its literal source assignment.
`WWOrdinalSyntaxPartialComputability.ordinalSyntaxPartialPrimitiveRecursive`
currently handles the all-left policy with `Primrec.nat_omega_rec'`. A general
selector supplies Computable assembly only. The new comparator deliberately
requires no primitive-recursive assembly and no policy-specific assumptions.

`ListFold` covers every finite input list and original left-to-right fold with a
jointly Computable step. `RankedRecursion` covers the complete actual recursive
specification: PR rank/finite child generator, strictly decreasing every child,
and an Option-valued Computable assembly that returns exactly the specified
result on actual child results. The proof must construct total computation of
f, not assume it. Arbitrary additional input state is retained in β.

Application to literal policy partials, including raw malformed codes and typed
exact syntax calibration, is a subsequent obligation. Abstraction/full source
assignment and arbitrary-policy equality remain unclaimed.
