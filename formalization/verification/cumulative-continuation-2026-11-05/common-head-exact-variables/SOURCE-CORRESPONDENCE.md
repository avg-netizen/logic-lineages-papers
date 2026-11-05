# Exact raw free variables for common-head compilation

Paper08, `08-multivariate-collapse-comparison/paper.tex`, `thm:common`, first sentence
(lines 870–874): each certified common-head comparison has an effective BASE formula
with the same raw free variables and the same truth at every positive valuation.

The unchanged `CommonSyntax`, `commonValue`, `headCodes`, `genuineHeads`, and original
BASE syntax/coding are used. The raw comparison compiler is retained literally and
followed by the finite conjunction of x=x for exactly the original pair support.
The empty conjunction is true. Only duplicates are removed from padding names.
Exact support is membership equality, not multiplicity or ordering. It is retained
for cancellation, constants, empty sums/heads, impossible signs and malformed raw
codes. Source semantics are quantified over all Nat-valued environments, which
includes the paper's positive environments. Coefficients remain positive by the
original stored-a-means-a+1 representation; no positive-level outside remainder
is admitted.

Five frozen targets separate raw semantics/support, literal code calibration,
typed source semantics and exact code support, actual raw support computation,
and actual total output computation. No new premise or oracle is introduced.
This advances the first source clause only. The full registered theorem remains
pending its unrestricted Boolean/quantified decision consequence.
