# Paper 17 independent source correspondence review

Reviewed baseline `dd4eddff9f8eab0a4532e8df4880f71b8d5dffb9`, tree
`c96d5298ebe9b1687f8b253367cc56765b4ed645`. This is a comparison of
the printed statements with the pinned Lean declarations, not a second
native gate and not a register change. The prior native evidence and
source digests are preserved.

## Closed blocks (#1418)

For the admitted finite topological circuit encodings and prepared closed
matrices, the comparator covers the printed existential, negated
existential and successful-domain universal queries at the factorial
control and at each fixed near control. Node references and original
wire updates carry repeated use of the same input/result; this is not a
claim about complexity or the syntactic absence of duplicated work.
The matrix predicates are weak linear inequalities, equality via the
two signs, and congruences with positive moduli. A universal quantifier
ranges over successful runs, not failures or malformed encodings.
Strict positivity of an integer row `r` is equivalent to `r - 1 ≥ 0`.

The former semantic caveat about `collapseWith` can be resolved from the
definitions: `OrdinalComparison/ParametricActualCollapseDefinitions.lean`
and `ParametricActualCollapseRecursionProof.lean` give the actual
well-founded finite predecessor maximum (zero bottom, otherwise recursive
values plus one), with membership and uniqueness below epsilon zero.
`OrdinalComparison/ActualOrdinalNorm.lean` gives the multiplicity-sensitive
Cantor-normal-form norm used in the predecessor bound.
`PermittedControl/ArbitraryFixedHeadCollapseSemanticProof.lean` aligns the
arbitrary normal-form head plus its tail with this same original ordinal
recursion. The comparator does not require replacing the printed collapse
by an abstract surrogate. The optional finite below-threshold extension
is represented by a finite guarded case split, not an extra native gate
constructor. No source correspondence blocker was found on the admitted
closed-block scope.

## Ground comparison (#1428)

`GroundComparison.GroundComparison` matches the fixed-policy theorem
in `sections/consequences.tex`, with a common typed ground context, arbitrary
result types, and the actual literal-policy assignment. The different
vector lengths have the explicit zero padding prescribed by the
manuscript. The selected generated-source/domain proofs give assignment
existence and independent positive-natural values for the admitted input
coordinates. The theorem handles typed codes, not an arbitrary malformed
source parser.

## Classification (#1429)

`GroundComparisonMain.MainComparison` combines #1428 with the literal
control-law and near-control modular facts (#010 and its companions) and
the original-term functional hardness (#339). The finite- and single-query
proofs construct the same literal `reduceCode strict` across policy and
control; the reduction correctness takes those parameters universally.
The paper's local sufficient control criteria are formalized; this does
not formalize all of Wilken--Weiermann's ambient presentation.

The positive clause has a remaining distinction. The Lean type proves
`forall p, Effective p -> exists computable decider`, using a common
parameterized mathematical construction, whereas the printed main theorem
expressly says "uniformly in a supplied computable admissible literal
parsing policy." It does not yet prove that a supplied policy program
index is mapped computably to a decider program index. The latter is the
stronger, literal uniform reading and should not be reported as checked.
A suitable strengthening is to calibrate a universal policy-indexed
interpreter to the existing selector, lift the actual ranked assignment
and query compilation to that interface, and specialize the resulting
joint program by its input code. On invalid or diverging policy indices
there is no totality requirement; a divergence must not be conflated
with a terminating malformed macro or non-applicable local rule.

The numbered register remains unchanged. The new review is evidence about
source correspondence, not owner approval to promote a numbered entry.
