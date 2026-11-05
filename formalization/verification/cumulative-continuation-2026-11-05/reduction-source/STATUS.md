# Exact RE-to-polynomial reduction

Target-only preflight: 1793880343782977604-2. First native exact proof gate:
1793880449073310856-2. Three aliases passed with only propext, Classical.choice
and Quot.sound. All 71 local import modules match successful native
source-bound receipts. Original targets and all supplier bytes are unchanged.
Independent review/adoption, including specialization review, is pending.

The final alias has precisely the original Targets.REPolynomialReduction type.
An actual RE predicate is represented as the zero-output graph of its partial
assertion function, preserving undefinedness. The proved ordinary-code graph
supplier yields Diophantinity, and the existing proved finite polynomial code
representation chooses one explicit finite code p for that fixed predicate.

Only then is the runtime reduction chosen: specializationCode p. Its proved
Primrec instance supplies Computable. Canonical codec faithfulness, preserved
well-formedness and exact zero-allowing natural-root correspondence establish
P(x) iff encodedPolynomialSolvable(specializationCode p x).

The quantifier order matters: for each fixed P and its RE proof, there exists
a fixed representing code and a computable function of x. No uniform procedure
for extracting p from an extensional Dioph, Poly or RE proof is asserted. The
actual source integer coefficients, original natural witness convention,
canonical codec, and malformed-code behavior are retained.

The original EncodedPolynomialUndecidable theorem and downstream comparison
undecidability statements are not yet asserted by this component.
