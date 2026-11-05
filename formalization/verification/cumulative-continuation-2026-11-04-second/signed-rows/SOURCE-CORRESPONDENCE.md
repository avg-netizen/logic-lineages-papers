# Signed translation and the complete hyper-collision branch

## Continuation and source scope

This package continues cumulative commit
`21972d84e10e03f17606fb9e7206dc92c863d73f` on
`formalization/cumulative-continuation-2026-11-04-second`. The preceding
constant-substitution and bounded-row package, earlier source introduction,
and newer PA addition laws retain their accepted source bytes and evidence.

The package advances paper08 `thm:snyatkov`, whose full first-order decision
endpoint remains pending. It addresses the restricted-normal-form closure gap
for signed unit translations and the complete three-way HyperWindow case II6.
The already accepted expanded-matrix collision and elimination theorems are
reused against the literal source guards and actual quantitative bounds.

## Exact signed translation

The replacement of original name `i` is the actual natural value
`((nu j : Int) + d).toNat`. This truncates a negative signed input to zero.
On the region `0 <= (nu j : Int) + d`, each original occurrence is translated:

| Original summand at name `i` | Translated summand | Constant correction |
|---|---|---|
| `x_i` | `x_j` | Its coefficient multiplied by `d`. |
| `Phi(x_i + e)` | `Phi(x_j + (d + e))` | Zero. |
| `Phi(H(x_i + e) + h)` | `Phi(H(x_j + (d + e)) + h)` | Zero. |

Occurrences at other names are unchanged. The construction preserves the
entire occurrence list in order, every coefficient, all multiplicities and
the original outer shifts. Zero and cancelled coefficients remain present.
Every translated output uses only the existing three summand constructors.

On that nonnegative region, the exact row-value theorem compares the
translated row under the original valuation with the original row under
`Function.update nu i replacement`. A separate exact theorem compares all
original occurrence domains. Neither statement discards the domain of a
zero-weight occurrence.

The formula core retains the existing Boolean structure and atom kinds.
Its exact support is `(v = j and i occurs originally) or
(v != i and v occurs originally)`. Coincident names are allowed.

## Total semantics across the truncation boundary

An unconditional shift-merging identity would be false below the translation
domain. The total compiler therefore uses the literal linear guard
`G := d + x_j >= 0` and constructs

`(G and core_translation(p)) or (not G and constant_substitution(i, 0, p))`.

The low branch reuses the previously checked numeral substitution. The exact
formula theorem has no nonnegative-anchor premise and holds under every
valuation, for arbitrary correlated Boolean bodies. Existing source domain
formulas remain at their original Boolean positions inside both copies of
the body. In particular, translating a guarded atom is equivalent to its
original meaningfulness and atom truth under the updated valuation.

The outer guard introduces `j` syntactically, so total output support is
exactly `v = j or (v != i and v occurs originally)`. This is the stated target,
including when the original formula omits `i`; no absent-name optimization
is assumed.

## The complete HyperWindow case II6

The new row guard is the conjunction of the two existing `guardedLe`
comparisons between the original hyper summands. It preserves both original
index domains, both original outer domains, and both coefficient-close
inequalities, including coefficient zero. Its evaluation is exactly that
of the unchanged `HyperWindow.closeMatrix`.

The three restricted-row outputs are:

| Alternative | Output construction | Remaining quantified name |
|---|---|---|
| Bounded original left variable | Existing bounded-row elimination at `HyperWindow.leftBound`. | `j` |
| Bounded original right variable | Existing bounded-row elimination at `HyperWindow.rightBound`. | `i` |
| Equal shifted hyper-indices | Total signed substitution `i := toNat(x_j + k - e)`, retaining the equality and original guard. | `j` |

The equality is represented by two opposite linear rows for
`e - k + x_i - x_j = 0`. Under the retained original index domains, this is
equivalent to equality of the existing total `HyperWindow.indexTerm` values.
The domain premise comes from the branch guard itself. Equality of truncated
indices alone is not treated as equality of arbitrary signed integers.

Each new branch is compared pointwise with the corresponding accepted
expanded-matrix branch applied to the compilation of the original row body.
The complete elimination theorem preserves the original `i != j` premise:
an existential over both names of the original guard and body is equivalent
to the disjunction of the three displayed single-name existentials. Every
other variable and all dependent occurrences retain the same valuation.

Exact support is an equivalence in all three branches. The left and equal
outputs contain precisely the original body names other than `i`, together
with `j`; the right output is symmetric. Both finite bounds are positive.
The original distinct-name premise is retained for this support theorem.

## Literal effectivity

The numeric programs use the unchanged item, row and atom encodings and the
radix-six Boolean formula encoding. Core translation performs actual integer
arithmetic and occurrence-list maps; the total program composes this with
literal Boolean guards and the accepted numeral-substitution program.
Malformed numeric atom payloads retain the explicit total decoder default.

The complete three HyperWindow branch programs use the original grouped
input layout, actual collision bounds, restricted-row guard encodings and
the signed-translation program. The body field is a radix-six row-formula
code. Expanded-matrix radix-eight constructors are not used as row encoders.
Exact literal calibration and primitive-recursion targets cover the actual
displayed programs, jointly in their inputs.

## Exact targets and remaining obligations

There are ten signed-translation targets: eight semantic/domain/support
targets and two numeric targets. There are six hyper-branch targets: original
guard calibration, pointwise calibration of all three branches, the complete
two-variable elimination clause, exact branch support, literal code calibration
and primitive recursiveness. The four definition/target files were frozen
after successful target-only preflight and before proof authorship.

The translation has unit slope. Arbitrary affine scaling can create
`Phi(a*x_j+e)`, and general anchors can introduce bare or nested `H`, outside
the current summand grammar. General Window/ReverseWindow anchors, purely
linear elimination, dominant boundary cases, branch exhaustiveness and the
global decreasing quantified-block induction remain separate obligations.
`EffectiveSourceExistentialNormalForm`, `EffectiveExpandedElimination` and
`FullSourceDecision` remain pending. No whole numbered source statement is
promoted by these supporting targets.
