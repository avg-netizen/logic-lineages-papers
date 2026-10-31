# The Wilken–Weiermann Comparison Problem

[Read the paper](paper.pdf) · [TeX source](paper.tex) · [Shared foundations](foundations.tex)

This is the entry paper for six manuscripts about termination orderings and
comparison of Wilken–Weiermann's canonical ordinal assignments to Gödel's T.
It explains the original questions, the precise remaining ground-input problem,
the proved positive and negative boundaries, and how the five companion papers
fit together. It also supplies the common mathematical foundation used by them.

The foundational proofs include an explicit maximum-predecessor algorithm,
the exact single-path collapse evaluator, its complete terminal-count identity,
strict finite-tail separation, and the actual-source forward translation.
The calculus, norm, control, admissible substitutions and canonical abstraction
rules are stated explicitly. Published background theorems are cited normally.

The literal assignment now fixes every finite-sum and padding convention.
Its forward translation and graded-domain results also hold separately for
each admissible fixed policy. Appendix A gives the full domain and bounded-norm
proofs, using a weak scalar inequality in place of the source's false strict
one. It exhibits a closed recursor-free source with positive assigned
coordinate 204 or 184 under two bracketing policies; the canonical comparison
problem therefore includes its parsing convention. The included
[source checks](repair/source-conventions/CONTROL.json) reconstruct this
witness without evaluating the collapse.

The five companions are included in this repository:

- [Termination ordering](../06-godel-t-termination-ordering/README.md).
- [Equality and one-variable comparison](../07-collapse-equality-and-one-variable/README.md).
- [Multivariate decidable fragments](../08-multivariate-collapse-comparison/README.md).
- [Actual-source arithmetic and undecidability boundaries](../09-canonical-source-expressivity/README.md).
- [Controlled descents and modular counts](../10-collapse-descent-and-modular-counts/README.md).

The exact standard-control comparison problem with several independent ground
inputs and unrestricted internal types remains open. A terminating evaluator,
a syntactic termination ordering, a complete-count attainment question and an
isolated intermediate block coefficient have different mathematical contracts.
The paper explains their relationships without identifying them.

Build with `python3 build_pdf.py` in this directory. Tectonic uses cached
resources by default; `--online` permits downloads on a fresh installation.
The script also supports pdfLaTeX. Computer Modern and AMS fonts are used.
All local TeX inputs are included. Reading the whole collection requires
the sibling directories; none of its new proofs depends on a private repository.

This is an AI-assisted hand-proof working manuscript for mathematical review.
Build and reference checks are documented in [VERIFICATION.md](VERIFICATION.md).
They do not constitute proof-assistant verification or independent human review.
