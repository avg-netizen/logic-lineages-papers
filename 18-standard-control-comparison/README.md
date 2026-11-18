# Identities and Comparison for the Standard Ordinal Collapse

**37-page explanatory manuscript, 17 November 2026.**
[Read the paper](paper.pdf) · [LaTeX source](paper.tex) · [Sources and scope](SOURCES.md)

The paper combines the earlier identity, one-variable and multivariate-fragment
developments for the unchanged control `G(n)=F_5(n+100)`. It gives complete
positive identity normal forms at arbitrary fixed heads, a finite-zero and
eventual-sign algorithm with one shared input, closed existential decisions
for polynomial heads, and parameter-preserving formulas for common-head and
balanced layers. A separate single-core result has a direct Presburger formula.

For sources whose free term variables all have ground type, the final section
states the literal canonical-source interface and derives universal equality,
one-name comparison, recursor-free comparison at arbitrary internal types,
and comparison through internal type level two. The first-order arithmetic theorem of A. S. Snyatkov
is cited with its exact hypotheses, which are verified for this particular G.

The paper merges the substantive material of earlier entries 07 and 08,
includes its common numerical foundations once, and retains the source-class
lemmas from entry 05. It does not claim unrestricted multivariate order
comparison at arbitrary standard-control heads or a full alternating theory
of the polynomial-collapse language.

The [collection guide](../COMPARISON-RESOLUTION-GUIDE.md) gives the current
organization, dependency map and relation to the preserved earlier editions.

## Build and verification

Run `python3 build_pdf.py` in this directory with Python 3 and a standard
TeX Live or MiKTeX installation. The script uses pdfLaTeX and, when a
BibTeX file is present, BibTeX; it downloads nothing. All mathematical
source inputs required to rebuild this PDF are included. Companion proofs
are cited conventionally with their exact imported interfaces stated.

[VERIFICATION.json](VERIFICATION.json) records the exact PDF, clean build,
isolated rebuild and page inspection. `SHA256SUMS` identifies this edition;
PDF metadata may make a later build's byte hash differ. The document checks
and AI-assisted hand review are not independent human verification, a
completed proof-assistant port, or a priority assessment. The repository's
formal target register remains authoritative for its older checked objects.
