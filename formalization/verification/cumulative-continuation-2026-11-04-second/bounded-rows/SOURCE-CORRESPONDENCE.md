# Restricted-row constant substitution and bounded elimination

## Merged base and source obligation

The continuation starts at merged main `1794804844e6f0de8def7bed4dc99b4c1a420e44`.
That base includes both the previous source-to-quantified-row package and the
new PA addition-law component. Their accepted source bytes and historical
evidence are preserved. The new branch is
`formalization/cumulative-continuation-2026-11-04-second`.

The present work advances paper08 `thm:snyatkov`, the decision theorem for
the literal first-order theory with `Phi(n) = F5(n + 100)`. The recorded
[normal-form closure gap](../../local-resume-2026-11-04-six-lanes/sol3-snyatkov/NORMAL-FORM-CLOSURE-SCOPE.md)
distinguishes the accepted expanded-matrix finite substitutions from outputs
in the restricted source occurrence-row grammar. This package closes constant
substitution and finite bounded elimination in that existing grammar, and
assembles two actual bounded branches using the already proved source bounds.

## Constant substitution without changing the grammar

The existing `NormalForm.Summand` has exactly three kinds: variables, shifted
`Phi`, and shifted `Phi(H(...))`. The new row operation fixes one original name
to a natural numeral. It evaluates each occurrence of that name with the
existing total arithmetic semantics and moves its weighted value into the
integer constant. Every other occurrence keeps its original order, coefficient,
name and signed shifts. Repeated and zero-weight occurrences are retained.

The substitution theorem holds under every valuation:

`rowValue (rowSubstitute i n row) ν = rowValue row (Function.update ν i n)`.

The remaining occurrence list is exactly the original list filtered by
`name != i`. The operation therefore stays inside the restricted grammar and
removes precisely the fixed name from syntactic support. Substitution is lifted
through both original atom constructors and every Boolean constructor, with
divisibility moduli and Boolean positions unchanged.

## Original domains survive removal of an occurrence

Constant folding removes occurrence metadata. The domain theorem records
exactly what must remain:

`rowMeaningful row (update ν i n)` is equivalent to
`fixedCutoff i row <= n` and meaningfulness of the residual row under `ν`.

`fixedCutoff` is the maximum original cutoff over **every** removed occurrence.
It does not inspect or simplify coefficients. An occurrence with coefficient
zero, or one cancelled arithmetically by another occurrence, still contributes
its original signed-domain condition.

Existing domain formulas are substituted at their existing Boolean positions.
The compiler does not regenerate a guard solely from the residual row. For
example, fixing the name in `Phi(x_i - 1)` to zero gives a total default value,
but its original domain guard remains false. Folding the numerical value does
not make that source occurrence meaningful. This distinction applies inside
negations and disjunctions as well as conjunctions.

## Bounded blocks and the existing source prefix

`bounded i B p` is the literal disjunction of `substitute i n p` for `n < B`.
Its evaluation is equivalent to `exists n, n < B and p.eval (update ν i n)`.
The bound is strict, matching the existing window constructions. Bound zero
produces falsity; support equivalence explicitly includes `0 < B`.

A right fold eliminates a finite list of bounded binders. Its semantics permits
repeated binder names with ordinary shadowing. Exact block support requires
that all listed bounds are positive, removes every listed name, and retains
every other original name.

The separate `ExactExistingPrefix` target ties this construction to the
unchanged `NormalForm.existsPrefix`. Its literal linear bound row is
`B - 1 - x_i >= 0`. For a duplicate-free list of names, block elimination is
equivalent to the existing existential prefix applied to the conjunction of
all bound rows and the original matrix. The duplicate-free premise is needed
because this source formulation checks bounds in the final valuation.

## Two actual source branches

The new branch guards use only existing summand constructors, signed rows and
`guardedAtom`. The row `-s + c*t >= 0` expresses the required comparison, and
its guard retains the original domains of both occurrences even when `c = 0`.

| Branch | Preserved source premise | Proved output |
|---|---|---|
| LinearWindow cases II3/II4 | An active nonlinear occurrence of `j` is at most the leading occurrence, which is at most `a*j`, with both original domains. | A literal restricted-row formula equivalent to the unrestricted existential over `j` of the original guard and any correlated Boolean row matrix. |
| ActiveHyper bounded alternative | The active hyper occurrence at `j` is at most the leading occurrence, which is at most `a*Phi(j+q)`, with all original domains. | The corresponding literal restricted-row finite elimination under the same shared valuation. |

The proof bridges each new guard to the **existing** expanded `LinearWindow.guard`
or `ActiveHyper.guard`, then uses the accepted actual quantitative bound.
Neither branch adds an independent-name premise: `i = j` is allowed. Exact
output support is `v != j` and either `v = i` or membership in the original body.
The actual numeric programs generate these restricted-row outputs, with exact
typed-code calibration and primitive-recursion proofs.

## Seventeen frozen targets and remaining boundary

The generic package has twelve exact targets: row substitution, exact residual
occurrences, original-domain splitting, formula substitution, exact substitution
support, bounded elimination and support, block elimination and support, the
existing-prefix bridge, literal numeric calibration, and actual primitive
recursion. The source-branch package has five: two actual elimination theorems,
exact branch support, literal branch calibration, and primitive recursion.

HyperWindow's finite-left and finite-right constructions are eligible for the
generic constant-substitution operation; their complete three-way assembly is
not an additional accepted target here. The equal-index branch substitutes a
signed affine expression and remains separate. General plus/minus anchors,
potentially nested hyper substitutions, variables occurring only linearly,
dominant boundary cases, branch exhaustiveness and the decreasing global
quantified-block induction remain unpaid.

Consequently `EffectiveSourceExistentialNormalForm`,
`EffectiveExpandedElimination` and `FullSourceDecision` remain pending. The
seventeen targets are supporting results and do not promote a whole numbered
source statement.
