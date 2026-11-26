# P17: executable closed evaluation on the encoded signed-bit family

Printed source: `arithmetic.tex`, `thm:arithmetic`, the zero-raw-coordinate base
case of the dimension recursion on exact graph and signed Boolean rows.

* Keep the literal encoded test, signed constant, original operand tape, and
  requested Boolean bit distinct. Tags 0/1/2 require payload zero; congruence
  tag 3 requires positive modulus. Unknown tags, invalid payload, and a row
  retaining operands reject the clause regardless of requested polarity.
* Evaluate genuine equality, nonnegative and positive signed tests; for a
  signed congruence, zero residue of the natural absolute value is equivalent
  to zero Euclidean residue of the original signed integer. Whole clauses
  require all the requested bits and the family accepts any true clause.
* Exact encoded clause/family equality to the typed closed evaluator holds
  even when a row is still open (it fails closed evaluation). At actual
  dimension zero the result is exactly typed existential satisfiability.
* Admission, signed test, row, clause, and family programs are primitive
  recursive. This is the closed case only, not a raw high compiler,
  broad malformed-domain validator, or effective original block solver.
