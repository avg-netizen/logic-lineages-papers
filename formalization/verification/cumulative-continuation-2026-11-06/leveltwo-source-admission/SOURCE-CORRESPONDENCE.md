# Exact original-source internal-level admission

Source: `08-multivariate-collapse-comparison/paper.tex`, `thm:leveltwo`,
lines 795–824. The supported input class uses the maximum internal type level
of the literal original term, including every subterm and binder type. This
component makes that class an exact numerical input test, then guards the
previously accepted source-to-counterexample compiler.

`Admission.test` reuses the original `Source.SyntaxCode.check` at every
visited node, and the existing exact numerical `typeLevel`. It is not a new
parser, type inference algorithm, or typed support enumeration. Application
visits both original children in the same context. Lambda visits its body
in the context extended by exactly the original domain type. Every actual
node result type is checked; all its subtypes have no greater level. In
particular the full lambda, case and recursor types count, not just their
annotation payloads or the final result type.

The calibration is against the unchanged `InternalLevelBound` and literal
`SourceTypeSupport.typeSupport`. It works in arbitrary original contexts and
at an arbitrary original result type. Unused high-level context entries are
not inserted into the support or bounded by this procedure. No beta
normalization or recursor-free restriction is imposed. Both directions of
typed admission preserve the exact original numeric code.

The ground-context wrapper recognizes exactly two actual original terms
with internal level at most two. `Admission.compile` calls the existing
`SourceCode.compile` unchanged on precisely this class and rejects other
inputs. Its output-existence criterion is exact, not merely a sufficient
test. Every returned package is linked back to genuine original terms,
actual canonical assignments, and the original positive-valuation
counterexample relation for weak, WW-strict and equality comparison.

## Boundary

Admission and translation are primitive recursive. Neither procedure
decides truth of the resulting closed existential package. No existential
solver, general word decision, guard/row completion, or undecidability claim
is introduced. The full numbered level-two theorem remains pending, and the
register remains unchanged. The current comparator is a supporting
input-domain and guarded-compilation theorem.

## Preflight correction

The unchanged repository placeholder scan rejected the initial new function
name `admit` before any Lean invocation. It was renamed to `typedAccepts`,
with no change to its definition or the target propositions' meaning.
Initial source and freeze snapshots remain in `rejected-reserved-identifier`.
No checker change or bypass occurred. The corrected definitions and targets
passed a separate native preflight before their successful proof gate.
