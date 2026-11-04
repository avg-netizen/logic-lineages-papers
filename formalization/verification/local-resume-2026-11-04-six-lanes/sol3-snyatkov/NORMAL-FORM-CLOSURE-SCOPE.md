# Finite elimination components do not yet prove source normal-form closure

The accepted Window and HyperWindow comparisons deliberately use arbitrary
expanded `Matrix` syntax and actual shared-valuation substitution. Their exact
theorems remove a quantified original name and their programs emit the literal
equivalent matrix. This is genuine multivariable elimination, with every
constraint retained. It does not prove that the output stays in the restricted
summand grammar of Snyatkov2008 Theorem1 display(1).

In particular, substituting a hyperfunction anchor into a name which itself
occurs under H can introduce nested H. The primary source's casesII2/II5
separate such active-hyper occurrences and use an additional small-variable
argument before the substitution. Those finite-bound subbranches and their
normal-form closure are not supplied by the generic plus/minus windows alone.
Case numbering in the S3 correspondence records identifies the source
quantitative/substitution step to which a component contributes; it does not
promote a whole normal-form-preserving case analysis.

The full unpaid chain must still fix the exact repeated-occurrence normal form,
prove closure of each selected branch, preserve original domains/free names,
and establish the source's decreasing induction measure. Allowing more expanded
terms in `Matrix` is useful for an honest intermediate semantics; it does not
make that restricted normal-form theorem true by definition. The full source
`FullSourceDecision`/`EffectiveExpandedElimination` targets remain uninhabited.
