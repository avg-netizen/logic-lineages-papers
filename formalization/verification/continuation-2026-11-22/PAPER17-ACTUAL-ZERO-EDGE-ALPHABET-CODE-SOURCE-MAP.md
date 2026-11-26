# Raw code for the original finite candidate alphabet

Companion to the exact typed expansion #917 and the depth collection
shape used in #918. [Paper 17 arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex)
130–162 fixes the prefix and H labels; 225–233 requires finite choices.

The raw prefix label keeps rank and original λ code and adds the
literal omega-square note to the original μ code. Only the literal
count tag supplies a prefix candidate. An emitted candidate prefix
key uses the existing literal rank and entry bytes. The candidate H
uses replacementCode with the original P endpoint pair first and Q
second; only strict lower Q.rank < higher P.rank is retained.
The list output retains original order, multiplicity, and source
keys, followed by prefixes and ordered H candidates.

The narrow numerical proof uses existing ordinalAddCodeEffective
and ordinalSubCodeEffective, typed raw tuples and list recursion;
it does not transitively import the unrelated general pair proof.
The exact typed calibration uses original note encode/add/sub
correspondence and literal list inductions. The code for iteration
recurs exactly once per independently supplied depth; its bounded
collector concatenates all depths from zero through the supplied
budget. No raw computation of the original signed structural charge
is asserted or used, and no alternative coarse budget is substituted.

The effectivity clauses are only for these particular total raw
list programs. Calibration is only on canonical typed operand
encodings. Candidate properness, actual collision/hit decisions,
future guard/terminal cutoff computation, full global-tail code,
symbolic branch generation and uniform normalization are not claimed.
