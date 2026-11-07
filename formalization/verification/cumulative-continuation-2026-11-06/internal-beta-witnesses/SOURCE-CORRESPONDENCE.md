# Exact source correspondence

OrdinaryArithmeticBetaDefinitions.betaBody specifies:
a = q * (((i+1)*b)+1) + r and r + succ(d) = ((i+1)*b)+1.
The new matrix is precisely this original conjunction, with q at Fin 2 index
0 and d at index 1. actualBetaMatrix proves equality of the embedded original
betaFormula and the existing finite existential block over that matrix.
It does not assert only semantic equivalence or change variable order.

Introduction substitutes the two chosen ordinary witness terms into this
matrix. Elimination preserves the existing finite-block eigenvariable
conditions, relabeling every ambient assumption and the result by Sum.inl.
The zero-code theorem uses the original multiplication-left-zero and
addition-left-zero derivations, not semantic evaluation or reflection.
