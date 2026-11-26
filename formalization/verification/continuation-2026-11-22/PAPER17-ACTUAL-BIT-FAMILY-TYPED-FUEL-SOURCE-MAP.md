# Paper 17: exact typed logical existential recursion on actual finite bit families

Printed source: `arithmetic.tex`, `thm:arithmetic`, descent on finite
free raw input support after exact low/high clauses.

- Defines one **noncomputable typed** Bool function from the already
  constructed same-family finite successor layer. At zero dimension
  it uses the exact constant checker; at positive dimension it searches
  actual children. No arbitrary-successor premise.
- Soundness holds for any fuel. Completeness uses the true union support
  dimension as a sufficient fuel, because every actual child strictly
  decreases it. The exact original typed signed/raw-value existence
  predicate is equivalent to true, and its negation to false.
- The supplied selected-control threshold condition is explicit. This is
  semantic/structural Lean recursion only: the typed `Finset.toList`,
  `Finsupp.support.toList`, shape tests and route-generation pipeline
  are not raw-effective by this result. No claim of traced
  computability, full original source circuit/quantifier interface,
  unrestricted decision theorem or `thm:arithmetic` completion.
