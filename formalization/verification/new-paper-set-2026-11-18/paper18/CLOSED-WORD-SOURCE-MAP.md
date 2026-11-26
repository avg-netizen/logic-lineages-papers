# Full current18 m:thm:existential comparator

Source: polynomial-arithmetic.tex word-language paragraphs at 343–367 and
complete theorem/proof at 504 onward. No arbitrary arithmetic or parameter
quantifier-elimination claim is imported.

## Literal syntax and source functions
PolynomialGraphCompletion.Letter tags 0,1,2,3,4 mean signed shift, Phi,
quadratic V, coherent signed X and counter E. Word is finite composition;
WordAllowed retains all degrees 3..D. Row is signed constant plus a finite
list of signed-coefficient (raw-name,Word) occurrences. No derived values
are made independent parameters. WordLinearDecisionCompletion.Formula
contains truth/falsehood, nonnegative rows, positive fixed-modulus congruence,
and all Boolean connectives. All row comparisons are expressible via sign,
negation and signed rows. Formula.tokens retains even zero coefficients.
Formula.meaningful asserts actual WordDomain of every original occurrence,
including negated atoms and syntactically inactive disjuncts.

## Explicit individual lower-bound adapter
ClosedWord.Bounds is an arbitrary finite (raw name,natural lower bound)
list. Duplicate names are harmless simultaneous constraints. withBounds
conjoins empty-word rows x-b>=0 OUTSIDE the original Boolean tree. Numeric
withBoundsCode builds exactly that syntax; Programs requires a genuine PR
fold and jointly Computable concrete solve(D,bounds,code), not a family or
an assumed decision oracle. Empty lists, constant matrices and bounds on
names absent from the original formula are retained.

BoundCalibration requires exact code/syntax, truth, degree and domain
correspondence. GeneralizedDecision retains bounds AND actual original
word domains AND original matrix truth. SourceDecision separately states
the literal printed theorem: under Adequate bounds, the semantic query is
bounds AND matrix truth ONLY. Adequate says every valuation satisfying the
bounds defines EVERY original occurrence; it is not an atom-truth premise,
row decision, tail supplier or termination oracle. This is precisely the
source's explicit domain requirement, not an extra assumption on a decider.
The generalized interface handles even bounds not paying all domains.

## Real proof route and exclusions
Use ClosedWordDecisionCompletion.Machine.solve, solve_computable, and
actualClosedDecision, whose full recursive dependency chain proves actual
finite branching, raw-name decrease, least stopping, correlated Cooper
elimination, finite-prefix evaluation and original global-domain semantics.
Fresh bound adapter proof must discharge syntax/domain/semantics and its
actual numerical computability. Complete conjunction is frozen before proofs.
No common-head/balanced full arithmetic, free-parameter QE, source assignment
frontend or arbitrary-policy computability follows from this theorem.
