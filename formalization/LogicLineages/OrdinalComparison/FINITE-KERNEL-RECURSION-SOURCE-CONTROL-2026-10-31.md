# Finite-degree signed block recurrence: exact checked boundary

The source is paper08 `paper.tex`, Lemma `lem:kernel-recursion`, lines265–298,
SHA256 `3c2bf4cb4d8b6145acf67ce14c3d818bd20c572b6547b07d57d8598b45940b25`.
The manuscript and its accepted baseline have not been changed.

The unsigned count and value recurrences are checked for every degree d>=2,
every retained mass c, and t>=c+2d+1. The actual maximal-predecessor descent,
not a newly defined recursive surrogate, supplies every count and value.
The exact shifted quadratic formula and a genuine uniform Computable encoded
count/value evaluator on all valid finite-degree inputs are also checked.
`FiniteKernelRecursionStatementChecks` receipt1793503919501675652-2 has five
exact aliases with only the standard three axioms.

For signed iteration, the same statement has genuine child meaning on the
explicit common tail max(c+2d+1,c+2|j|+3) when d>=3 or j>=0. This is a
CORRECTED-DOMAIN supplier, not the printed unrestricted whole lemma. The
ordinary source cocycle and integer-to-natural iteration arithmetic prove it.
No comparison, termination, count, or domain oracle is supplied.

At d=2 and j=-1, the right child would be degree one at offset-1. Its
iteration depth is always zero, whereas the left depth is positive on the
stated tail. The source requires a positive depth: no amount of increasing
the input repairs that missing child domain.

Even silently changing the convention to clamp nonpositive depths to zero
would not save the printed unrestricted recurrence. For d=2,j=-2 and EVERY
t>=c+7, write E=E^2_(c+2)(t) and u=X^2_(c+2)(t). Then E>=2 and the literal
unsigned cocycle gives E^2_c(t)=E+1. The left side is f^[E-1](t), while the
zero-clamped right child is u=f^[E](t); strict increase of f gives a strict
inequality. The left source depth is positive, and the right source depth
is -1. This precise total-extension counterexample is checked by
`FiniteKernelNegativeRecursionStatementChecks`, receipt1793504009362802814-2,
standard three axioms. It does not assign a source meaning to the undefined
child. The degree-two formula V_(j-ceil(c/2)) itself remains valid.

Consequently the original lemma remains pending for source repair or an
explicitly approved domain qualification. These two component acceptances
add ZERO numbered source completions. Whole07 and whole08 single-core
acceptances remain unchanged. No private research, Lean resource limit,
compiler helper, package root, target register or publication was altered.
