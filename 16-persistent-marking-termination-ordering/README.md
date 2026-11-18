# A Decidable Path Ordering for Gödel's T with Bachmann–Howard Descending Height

**29-page explanatory manuscript, 17 November 2026.**
[Read the paper](paper.pdf) · [LaTeX source](paper.tex) · [Sources and proof scope](SOURCES.md)

The paper defines one persistent-mark weak/strict pair on literal typed terms,
proves both comparisons decidable, proves context and substitution stability,
orients the original beta, case and recursor reductions, and identifies its
descending height as the Bachmann–Howard ordinal. Its restriction to an actual
disjoint ranked ground signature is multiset recursive path ordering.

The proof includes the complete composition appendix, finite observation
semantics, numbered positive-path simulation, arithmetic accessibility argument,
native ordinal iterators, and matching published ordinal calibration. It works
with open terms and functional free variables. It is independent of the
[numerical companion](../17-permitted-control-canonical-comparison/README.md).

The [consolidation guide](../COMPARISON-RESOLUTION-GUIDE.md) explains why the
new II5 exposition has two papers and how it relates to earlier entries 05–10.
The earlier relation's checked composition obstruction is preserved. The new
paper changes the already-marked strict case and supplies proofs for that
new definition; it does not certify the earlier definition.

## Build and review

Run `python3 build_pdf.py` here with Python 3 and a standard TeX Live or MiKTeX
installation. The script runs pdfLaTeX and BibTeX; it downloads nothing. All
required sources are contained in this directory. The PDF uses embedded
Latin Modern and AMS fonts. `SHA256SUMS` identifies this edition; PDF metadata
can change its byte hash on a later rebuild.

The build has no unresolved references or layout warnings. All 29 pages were
visually inspected; the final citation correction and the reflowed appendix
were inspected again. [VERIFICATION.json](VERIFICATION.json) pins the PDF and
build observations. These are AI-assisted hand proofs, not a completed Lean
formalization or an independent human review. Existing formal target counts
are unchanged.
