# Balanced source translation and program provenance

The original BalancedExactVariables source formula, exact support proof, actual
sign semantics, typed code calibration and all-code output computation are reused
without changes. They already account for the whole shared basis, positive head
coefficients, zero outside multiples, canceled terms and support padding. This
package does not rebuild balanced collection, strict intervals, finite boxes or
the actual head evaluation program.

Its new source AST records every atom's own original typed shape/certificate/pair.
Positive existence is compiled to ordinary SourceFormula existence with the literal
0<x guard inside the binder. Correctness propagates positivity on the original
free-name set through negation, conjunction and binder update; it does not guard
individual atoms or silently strengthen a negated source formula's domain.

Raw radix-four source codes use explicit Encodable payload decoding and a fixed
empty-shape/zero default. Non-atomic codes recurse only on strictly smaller child
codes. The finite decreasing graph computes the actual recursive code transform.
Atoms call the unchanged balanced output compiler, then the existing literal BASE
to SourceFormula code compiler. The output is ordinary radix-five SourceFormula
syntax, not a new semantic interpreter or truth oracle. No complexity bound or
primitive-recursiveness claim for the whole compiler is made.
