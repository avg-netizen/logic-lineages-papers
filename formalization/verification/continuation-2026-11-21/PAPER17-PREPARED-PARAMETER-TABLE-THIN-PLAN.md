# Paper 17: thin prepared-parameter projection plan (not a proof)

See the independently read `PAPER17-ONE-VARIABLE-COOPER-BRIDGE-SOURCE-REVIEW.md`
for the actual checked formula-valued Cooper kernel and pinned sources.
A prepared-row encoding can avoid re-traversing the output to make new
field expressions.

- Use a literal immutable table of lower semantic operands. Each slot
  records a raw lower rank, an ordinary field code with its original
  lower rank, or a count's endpoint codes with its original lower rank.
  Distinct slots need not be mathematically independent. A duplicate
  occurrence may use the same slot, or separate slots whose evaluation
  is tied to the identical original coordinate and data. No table entry
  may refer to the eliminated greatest raw coordinate.
- Store the prepared Boolean signed-row formula using the existing pure
  `NormalForm.Summand.variable` encoding. Name **0** is uniquely the
  actual eliminated raw natural. Positive name `j+1` is the literal
  original table slot `j`. Require bounded name support and plain-variable
  constructor grammar (including coefficient-zero occurrences).
- The new raw operation can be just **retain the exact table bytes,
  run `LinearRows.Code.eliminate 0` on the formula code**. It is a genuine
  raw program, not compiler semantics using function input as oracle.
  Calibrate literal syntax code as checked. The encoded output need not
  expand the table back into a new field AST: its exact unchanged table
  is the lowering map, and any later consumer reads the same index.
  If a consumer eventually needs literal expansion, it is an optional
  effective lookup, not part of deciding this prepared projection.
- Prove the existing row operations and substitution preserve the pure
  constructor grammar (support alone cannot establish this). Exact
  variable-name support then proves no name zero in the result and no
  reference outside the original table. Output can retain unused table
  entries without inventing field occurrences.
- For every assignment to slots, the untouched formula's evaluation
  under update of name zero is equivalent to the output's evaluation
  by the existing checked arbitrary-assignment theorem. A corollary
  may evaluate the same table at a single original lower valuation
  with the actual fields and definedness, not existentially quantify
  over tuple entries. Prove the original raw valuation extension at
  the eliminated coordinate leaves all lower table entries untouched.
- Keep earlier source-domain and graph constraints at their genuine
  Boolean positions. This supplier starts at a **prepared** signed
  Boolean row (no nonlinear occurrence of zero). It does not prove
  actual field/residue normalization to such a row, count replacement,
  source flattening, finite low strips, iteration across all dimensions,
  full Presburger arithmetic or any numbered theorem.

This records a potentially thinner next formal target, with no Lean
source, compiler effect, or accepted status.
