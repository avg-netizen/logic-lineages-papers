# Actual terminal tests on the original mixed graph

Paper 17, `17-permitted-control-canonical-comparison/sections/arithmetic.tex`, lines 3–19 and 33–48. Adds the exact original terminal test to the accepted normalized mixed graph #994 at a supplied external valuation.

- The suffix is an actual supported Boolean signed-row formula on named outputs (plain `NormalForm.Formula`, using its literal signed rows and positive-modulus convention), or the exact existing admitted bounded source test (`BoundedSource.test` and `BoundedSource.answer`). The signed-row evaluator uses the actual row value and equivalent exact integer remainder test. Neither case rewrites term names or makes independent copies of shared wire values.
- The maximum is derived from all literal suffix names, including listed bounded binders. Its free input support is proved stable under the canonical hidden lift; bound test values retain their original local updates. Thus actual test truth and the fitted Boolean answer are unchanged by normalization.
- For a fixed supplied original external valuation, run the actual sequential circuit and then evaluate the original suffix at its actual final output values. Failure is a separate `none`; false and true each require a positive normalized computational graph and exact original exterior agreement. Test polarity alone flips.
- This is not a parser, a claim that all possible terminal syntaxes are covered, effectivity of a coded circuit driver, a uniform low/high split, or a closed arithmetic decision-procedure claim.
