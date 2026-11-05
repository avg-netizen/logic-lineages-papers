# Quantified linear-name fragment: source correspondence

This component continues the source-row elimination programme for paper 08's
Snyatkov BASE theorem. Its input is the existing `SourceRows.QFormula`, not a
new semantics chosen to make the result true. The formula retains original
Boolean positions, named existential binders, repeated binder names and
shadowing. Universal quantifiers are expressible through negation and
existential quantification; no binder is commuted across a Boolean node.

The exact admissibility test requires every occurrence bound by a binder to
be the literal `NormalForm.Summand.variable` with that binder's name. It checks
free occurrences relative to the immediate body, so an inner binder shadows
an outer binder of the same name. Nonlinear `phi` and `hyperPhi` summands at
free names remain arbitrary correlated parameters. Zero coefficients,
repeated names, cancelled weights and the original domain formulas remain
literal input data; no nonzero-coefficient simplification changes the test.

The compiler recursively preserves negation/conjunction and invokes the
already verified `LinearRows.eliminate` at each named binder. Correctness is
claimed only under the frozen admissibility test. Its unconditional support
lemmas assert exact membership of the remaining literal summand values and
free names. They do not assert multiplicity, list order or row coefficient
preservation. The compiler's output-linearity test equals the input's exact
free-linearity test, permitting subsequent binders to use the established
one-name theorem with no additional oracle or semantic premise.

The block compatibility target connects directly to the earlier
`SourceRows.bindAll` and `LinearBlock` APIs, including repeated names. The
all-code numeric programs recurse on the existing radix-four quantified-row
encoding. Literal typed-to-numeric calibration and primitive recursiveness
are separate exact targets, not an assumed computable evaluator.

This is a restricted-fragment quantifier-elimination result, not general
Snyatkov BASE decision or elimination of nonlinear bound occurrences.
Nonlinear anchors, active-hyper assembly, dominant boundaries, exhaustive
source-case selection and the global source induction remain pending. No
numbered source-register statement is promoted by this supporting component.
