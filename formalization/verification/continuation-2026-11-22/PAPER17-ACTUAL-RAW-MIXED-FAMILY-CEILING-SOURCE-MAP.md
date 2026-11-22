# Paper 17: executable upper cutoff for the actual literal mixed ranked family

Printed source: `arithmetic.tex`, the finite common-cutoff
step for a fixed raw coordinate order branch.

- Keep the original read bound before cleanup for every literal term,
  including zero signed weights. Signed tests use the exact cleaned
  syntax and signed constant in the checked common/sign majorants.
  Congruence tests use the exact original operandwise maximum for the
  same unsigned modulus, with its original literal ordered terms.
- The encoded row cost covers the exact typed row need (inequality for
  the signed budget, exact modular cost). PR finite maxima compose
  over rows and clauses. For a raw family the safe bound may retain
  costs of clauses omitted by the typed proper-clause filter; it does
  not declare those clauses proper.
- This is a literal rank-branch family bound for a supplied width
  and original source threshold. It is not a claim that one actual
  valuation pays the bound, nor an implementation of high-route
  selection, shared packet effects, or whole solver/printed theorem.
