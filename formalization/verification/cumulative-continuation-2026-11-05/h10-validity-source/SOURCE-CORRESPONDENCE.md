# Original H10 polynomial input validation

This component recognizes exactly the original `PolynomialCircuit.decode`
followed by `PolynomialCircuit.Code.WellFormed`. It runs before domain shifting
or positive-circuit compilation.

- The parser is unchanged. The input begins with the original input arity.
  Every signed coefficient record has its original tag, magnitude and explicit
  variable-list length frame. Truncated records, invalid tags and invalid
  length frames fail exactly when the source decoder fails.
- Every original variable occurrence must be below that original arity.
  Validation includes repeated indices and indices in zero-coefficient terms.
  The latter is required by the literal source `WellFormed` predicate, even
  though a later polynomial compiler can discard the zero term.
- This prevents an invalid original variable from being mistaken for a later
  compiled auxiliary gate with the same natural index.
- Empty monomial lists, constant monomials, repeated monomials and arbitrary
  signed coefficients retain their source behavior. No polynomial
  normalization or quotient representation is substituted.
- The public numeric endpoint is `validInput : List Nat → Bool`. Its exact
  arbitrary-list specification is:
  `validInput xs = true` iff there exists a decoded code with the original
  `WellFormed` property.
- The primitive-recursion proof uses the actual length-framed `decodeTerms`
  parser and the standard Int operations. No alternative Int encoding and no
  `Primcodable PolynomialCircuit.Code` instance is introduced. A raw-list case
  split handles the header, so only the standard List Nat/Bool encodings occur
  in the final effectivity statement.

Definitions and target propositions were frozen before proof authoring.
Preflight passed in `preflight/1793882212553941866-2.json`.

This is malformed-input and arity validation only. It does not claim the full
H10 reduction, polynomial satisfiability correspondence or downstream hardness.
