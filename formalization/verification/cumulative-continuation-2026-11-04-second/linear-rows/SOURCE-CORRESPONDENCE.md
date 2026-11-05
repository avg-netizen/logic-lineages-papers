# Effective elimination of a linear name in source rows

## Source scope

This package continues cumulative commit
`30af8ce523e32a8d26d2072642a152fd51314960` on
`formalization/cumulative-continuation-2026-11-04-second`. The preceding plain-Phi
windows, signed translation, hyper-collision, bounded substitution, source
introduction and PA addition-law packages remain unchanged.

The arithmetic supplier for paper08 `thm:snyatkov` still requires a complete
effective elimination procedure. This package closes its linear-name step
for the existing restricted occurrence-row grammar. The same parameter
discipline appears explicitly in the proof of `thm:existential` in
`08-multivariate-collapse-comparison/paper.tex`: nonlinear terms at other
original names remain parameters under their common valuation. The present
package does not claim the more general finite-degree word grammar of that
separate theorem.

A source row remains an integer constant plus a finite occurrence list of
integer-weighted `variable`, `phi` and `hyperPhi` summands. Repeated occurrences,
different shifts, signed coefficients and zero weights remain literal data.
The input may be any Boolean combination of nonnegative rows and positive
modulus divisibility atoms.

## Exact linearity and the original valuation

For a selected original name `i`, `isLinear i p` inspects every occurrence in
every atom. An occurrence named `i` must be precisely `Summand.variable i`.
A zero coefficient does not exempt a nonlinear occurrence. Nonlinear
occurrences at every other name are unrestricted.

The algorithm extracts the integer coefficient

`leading i r = sum of weights of occurrences named i`

and the literal remainder obtained by removing those occurrences. The
frozen row-splitting target is

`rowValue r (update nu i n) = rowValue (remainder i r) nu + leading i r * n`.

It holds under the exact syntactic linearity condition. Every remainder is
evaluated under the same original `nu`; no derived nonlinear value is
introduced as an independently quantified witness.

The proof interprets a symbolic remainder as the constant affine form
`Affine.const (rowValue r nu) : Affine 0`, and an original row as an
`Affine 1` with that remainder constant and the extracted coefficient.
This interpretation is proof-side only. The executable algorithm takes rows
and names, with no valuation, evaluator or semantic oracle as an input.
Row addition and scaling commute with the interpretation, allowing exact
reuse of the already accepted Forests Presburger normalization and unit
elimination theorems.

## Literal normalization and finite elimination

The coefficient modulus is the product, over all source atom occurrences,
of `1` for a zero coefficient and the coefficient's natural absolute value
otherwise. Its positivity is a separate frozen target.

For a nonzero coefficient `a`, adjustment scales the remainder by
`M / natAbs a` and replaces the coefficient by its sign. Divisibility
moduli are scaled by the same factor. Zero coefficients retain the literal
remainder with sign zero. The normalized formula keeps the actual `M | y`
constraint needed to relate the normalized natural witness to the original
one.

Unit elimination computes the product of positive atom periods and retains
zero and every inequality cutoff. It instantiates the formula at every
cutoff plus every residue below the computed period, and takes their finite
disjunction. Each instantiated formula includes the actual nonnegative
witness guard. This is elimination over natural witnesses, including zero.
The list casts in the frozen code retain the literal natural-to-integer
candidate conversion.

The principal correctness target is

`(eliminate i p).eval nu <-> exists n : Nat, p.eval (update nu i n)`

under `isLinear i p = true`. The unit-elimination target is unconditional
over all symbolic unit formulas because its extra scalar argument is
separate from the named valuation.

Original domain formulas remain ordinary formulas at their existing Boolean
positions. The guarded-atom target explicitly retains both
`rowMeaningful a.row (update nu i n)` and the original atom's truth under
that same update. Semantic row equality alone is not used to discard
source domains.

## Exact output support and effectivity

The output-support target has no linearity premise:

`v in (eliminate i p).variables <-> v != i and v in p.variables`.

Scaling preserves occurrence lists even when its factor is zero. Every
instantiated normalized atom retains its residual occurrences, all cutoff
names come from those same rows, and the zero cutoff with residue zero
exists because the period is positive. Thus the result establishes exact
support, including syntactically retained zero coefficients.

The numeric construction uses the existing row and summand payloads and
the existing radix-six Boolean encoding. Unit atoms add a literal integer
sign field. Two structural recursions map atom payloads and collect atom
payloads; row arithmetic, filtering, products, cutoffs and finite candidate
enumeration then compose them into the complete compiler.

The programs are total on all numeric inputs, with fixed defaults for
undecodable payloads. Literal calibration is unconditional for actual typed
syntax. Primitive-recursion claims apply to the actual numeric linearity
test, normalization, unit elimination and full eliminator, jointly in the
selected name and formula code where applicable. No practical complexity
bound is claimed for the finite residue enumeration.

## Frozen targets and remaining work

The three definition/target files were frozen after successful target-only
preflight and before proof authorship. Their twelve targets comprise row
arithmetic, exact row splitting, the syntactic test, positive coefficient
modulus, positive unit period, normalization, unit elimination, source
elimination, exact support, guarded-atom elimination, literal numeric
calibration and primitive recursiveness.

General nonlinear anchors, active-hyper source-case assembly, general affine
substitution inside nonlinear arguments, dominant boundary cases, exhaustive branch selection and
the global decreasing quantified-block induction remain separate obligations.
`EffectiveSourceExistentialNormalForm`, `EffectiveExpandedElimination` and
`FullSourceDecision` remain pending. No whole numbered source statement or
separate PA recursion endpoint is promoted by this supporting package.
