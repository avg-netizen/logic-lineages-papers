# Nested translation and both plain-Phi windows

## Continuation and exact scope

This package continues cumulative commit
`b2a24584a3615b0d1a51a531530afdbaf2d75ded` on
`formalization/cumulative-continuation-2026-11-04-second`. It preserves the
accepted bounded-row, signed-translation and hyper-collision packages, earlier
source introduction, and the newer PA addition laws.

The new work advances paper08 `thm:snyatkov` through the plain-Phi
specializations of both accepted generic finite windows. The anchor is the
actual shifted original variable `shiftTerm (.variable j) k`; the compared
summands are `Phi(x_i+e)` and `Phi(x_j+k)`. Arbitrary original signed shifts,
coefficients and correlated Boolean row bodies are retained. The output stays
in the unchanged three-summand occurrence-row grammar.

This does not complete the arbitrary-anchor source cases. An anchor containing
hyperfunctions, inverses or several names may still leave the restricted
grammar under substitution.

## Two literal truncations

The shared nested substitution replaces name `i` by

`toNat (toNat ((nu j : Int) + a) + b)`,

where the inner natural value is cast to `Int` before adding `b`. It splits on
the literal guard `G := x_j + a >= 0`:

`(G and SignedRows.substitute i j (a+b) p) or
(not G and BoundedRows.substitute i b.toNat p)`.

The theorem is unconditional over every valuation, including coincident names.
Existing source domain formulas remain at their original Boolean positions
inside both copies of the body. The guarded-atom theorem compares the result
with the original row meaningfulness and atom truth under that same updated
valuation. Zero or cancelled coefficients do not remove original domains.

Exact output support is `v = j or (v != i and v occurs originally)`. The case
guard introduces `j` even when the original formula omits `i`; the stated
support theorem records this fact explicitly.

## Literal forward and reverse candidates

Both old source candidates are matched at every valuation:

| Source replacement | Inner shift `a` | Outer shift `b` |
|---|---|---|
| `replacementTerm (shiftTerm (.variable j) k) e d` | `k` | `(d : Int) - e` |
| `ReverseWindow.replacementTerm (shiftTerm (.variable j) k) e d` | `k - (d : Int)` | `-e` |

The reverse identity uses the actual natural subtraction:
`z.toNat - d = (z - (d : Int)).toNat` for natural `d`. Directly combining all
shifts is generally false. For example, with `x_j=0`, `k=0`, `d=1`, `e=-2`,
the original reverse replacement is `2`, while the single merged signed
translation would yield `1`. The nested construction retains the correct
default below the displacement bound without adding a domain premise.

## Original guards and finite elimination

The forward guard asserts

`Phi(x_j+k) <= Phi(x_i+e) <= c * Phi(x_j+k)`;

the reverse guard asserts

`Phi(x_i+e) <= Phi(x_j+k) <= c * Phi(x_i+e)`.

Both are conjunctions of the existing `FiniteBranchRows.guardedLe` formulas.
They retain both original signed Phi domains, including coefficient zero.

The older generic `Window.closeMatrix` and `ReverseWindow.closeMatrix` retain
the eliminated name's domain, while their arbitrary anchor is total syntax.
The precise source comparison therefore keeps the original anchor-domain
formula explicitly in the old body:

`Matrix.conjunction (shiftDomain (.variable j) k) p.compile`.

Each new finite output is the literal disjunction over `List.range (c+1)` of
the corresponding nested substitution into the new guard conjoined with the
original body. Candidate and full-output calibration permit coincident names.
They compare every result pointwise with the corresponding accepted expanded
finite window and its explicit anchor-domain body.

Actual existential elimination retains `i != j`, exactly the independence
needed for the shifted anchor to omit the eliminated name. In each orientation,
the source existential over `i`, with the comparison, both original domains
and arbitrary correlated Boolean body, is equivalent to the new quantifier-free
row output. No witness for a derived nonlinear value is chosen independently.

Exact support in both outputs is
`v != i and (v = j or v occurs in the original body)`. The enumeration is
nonempty for every coefficient because it has `c+1` candidates. Every other
original variable remains under the same valuation.

## Literal effectivity and exact targets

The new numeric input explicitly stores both names, both signed shifts, the
coefficient and a radix-six row-formula body code. The old generic anchor-code
slot is not silently reinterpreted. Numeric guards use the existing row/item
encodings and radix-six Boolean constructors; the complete programs enumerate
the actual `c+1` source candidates and invoke the concrete nested-substitution
program. Literal typed-code calibration and primitive-recursion targets cover
the displayed programs jointly in their inputs.

There are five nested-translation targets: total substitution, exact support,
guarded-atom semantics, literal code calibration and primitive recursiveness.
There are seven plain-window targets: original guard calibration, both literal
candidate substitutions, both finite-output calibrations, actual elimination
in both orientations, exact support, literal code calibration and primitive
recursiveness. The four definition/target files were frozen after successful
target-only preflight and before proof authorship.

## Remaining obligations

General nonlinear anchors, active-hyper source-case assembly, arbitrary affine
scaling, purely linear elimination, dominant boundary cases, exhaustive branch
selection and the global decreasing quantified-block induction remain separate.
The existing Forests Presburger solver is available for later reuse; the
correlated row-to-affine bridge, pullback and uniform numeric effectivity still
need exact source gates.

`EffectiveSourceExistentialNormalForm`, `EffectiveExpandedElimination` and
`FullSourceDecision` remain pending. These supporting results do not promote
a whole numbered source statement or the separate PA recursion endpoint.
