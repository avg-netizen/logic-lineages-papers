# The domain of hyperreal differentiation is always proper

[Paper (PDF)](paper.pdf) · [Canonical TeX](paper.tex) · [Sources](SOURCES.md) · [Verification](VERIFICATION.md)

Alexander and Dawson ask whether the differentiation domain in their ultrapower can be the whole hyperreal field, and whether the answer depends on the admissible idempotent ultrafilter. This paper proves that the domain is proper for every such ultrafilter. Its bounded positive witness has **every** equivalent representative discontinuous on an ultrafilter-large set. The excluded element is a positive infinitesimal, which also proves that the domain is not order convex.

The six-page account explains the quotient, the source derivative and the representative quantifier before giving the Hamel-coordinate dichotomy. The witness may depend on the ultrafilter and need not be measurable. All local proofs are included; no private project conventions are needed.

Build with `python3 build_pdf.py` in this directory. It uses cached Tectonic resources or pdfLaTeX. On a new installation, `--online` permits missing TeX resources to be fetched. The local preamble selects Computer Modern.

This is an AI-assisted hand-proof manuscript for review, without formal certification or an established claim of historical priority.
