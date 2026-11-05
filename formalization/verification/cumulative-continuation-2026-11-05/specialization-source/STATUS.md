# Explicit computable polynomial specialization

Target-only preflight: 1793879650877233876-2. Final exact gate:
1793880153930579281-2. Five aliases passed with standard axioms only.
The 20-module local import closure matches successful source-bound native
rows. Three failed proof candidates/logs are preserved. The comparator,
definitions and prior suppliers stayed unchanged after successful preflight.
Independent review/adoption is pending.

The input is the existing explicit finite integer-monomial Code. Substituting
natural x for variable zero multiplies each coefficient by x to the number of
zero occurrences, deletes those occurrences, and shifts every remaining index
down by one. Repeated variables, duplicate monomials, zero coefficients, empty
monomials, x=0 and zero auxiliary witnesses retain their literal meanings.

The exact original integer-polynomial interpretation is proved for arbitrary
remaining integer valuations. Well-formedness is preserved. The natural-root
correspondence uses the original joinedNat first-parameter/auxiliary split and
the original zero-allowing HasNonnegativeRoot predicate.

The actual natural-number specializationCode function builds the canonical
list encoding explicitly. Negative coefficients that become zero use the zero
tag, not negative zero. For each fixed finite code p, its runtime function in
x is proved primitive recursive, and exactly matches encode(encode(specialize
x p)). No Primcodable structure or oracle for abstract polynomial proofs is
used to assert effectiveness.

One may choose a finite representing polynomial existentially for a fixed
predicate, then use this checked numeric function. This does not provide an
algorithm that extracts codes from arbitrary Dioph or Poly proofs. The exact
REPolynomialReduction and EncodedPolynomialUndecidable targets remain pending.
