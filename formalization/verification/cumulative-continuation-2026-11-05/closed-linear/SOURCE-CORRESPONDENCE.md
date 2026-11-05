# Closed admissible linear sentences: source correspondence

This component is the executable decision endpoint for the restricted
quantified-row fragment. It uses the existing `SourceRows.QFormula` syntax
and semantics and the exact `QuantifiedLinear.admissible` test. It does not
claim the full BASE decision theorem of paper 08.

A sentence must have no syntactically free names. This is literal support,
including zero-weight and cancelled row occurrences, not semantic
independence. Quantifier elimination preserves that support exactly, so the
output of a closed sentence has rows containing only integer constants.
The Boolean evaluator then uses integer sign, natural absolute value,
remainder and Boolean operations. It requires no evaluator for Phi or H.

`decideClosed` returns `none` precisely when the input fails admissibility
or closedness. An out-of-fragment rejection is not a false-sentence answer.
For an admissible closed input, a returned Boolean agrees with the original
formula under every environment. The algorithm preserves all original
Boolean and binder semantics through the preceding elimination theorem.

The numeric endpoint uses existing source-row and normal-form encodings,
with separately targeted literal calibration and primitive recursiveness.
On malformed numeric inputs the helper programs are total, but semantic
claims apply only to the encodings of the existing typed syntax.

General elimination of nonlinear bound occurrences remains pending, as do
the nonlinear source assemblies and global BASE induction. This component
makes no source-register status promotion.
