# Equality and one-variable comparison for positive collapse expressions

Read [paper.pdf](paper.pdf). The canonical source is [paper.tex](paper.tex).

The input language uses the actual fixed-standard-control functions
`h_lambda(n) = psi(lambda+n)`, positive variables, natural constants and
addition. Closed limit indices and nesting are unrestricted. The paper proves:

- Universal equality has a complete recursive normal form with any finite
  number of independent positive inputs.
- With one shared input, a nonidentity has a computably bounded finite zero set.
- With one shared input, eventual sign is computable; finite-prefix evaluation
  decides existential or universal Boolean combinations of equality and order
  atoms.

The proof includes the kernel suppliers rather than directing the reader to
private notebooks: exact prefix cuts, count comparison, complete profile
reserves, cross-mass and limit-mass packing, successor count cocycles, the
all-principal mass induction, and the mutual comparison/cut-certificate
algorithm with its well-founded measure. Worked examples explain the positive
normal form, nested comparison and the special mass ties at omega squared.

The included [foundations paper](../05-wilken-weiermann-foundations/paper.pdf)
supplies the maximal-predecessor evaluator, complete-count formula, control
growth and actual-source translation. Standard published background need not
be reproved here. The results concern actual collapse heads; this is different
from the earlier public paper on the elementary `2^f g` expression language.

Inner subtraction, open multiplication and variable ordinal indices are not
constructors. Multivariate identity is distinct from existential equality;
the order algorithm requires one *shared* free name across the query.

Build with `python3 build_pdf.py` (cached Tectonic by default, or standard
pdfLaTeX). The local preamble uses Computer Modern and AMS mathematical fonts.
[SOURCES.md](SOURCES.md), [PROVENANCE.json](PROVENANCE.json) and
[VALIDATION.md](VALIDATION.md) supply editorial provenance and document checks.
The manuscript is a hand proof, with no practical running-time or formal
verification claim.
