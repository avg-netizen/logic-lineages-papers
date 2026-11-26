# Decidable Ground Comparison for Norm-Controlled Ordinal Assignments

**30-page explanatory manuscript, 17 November 2026.**
[Read the paper](paper.pdf) · [LaTeX source](paper.tex) · [Sources and corrections](SOURCES.md)

For explicit controls allowed by the Wilken–Weiermann framework, the paper
decides universal weak comparison, strict comparison and equality of literal
canonical assignments whenever all free term variables have ground type.
Internal types, bound-variable types, result types, recursors and finite
nesting are unrestricted. The same controls give undecidability of weak and
strict comparison with functional free inputs, with the stated low internal
type bounds.
The unchanged standard control also has this functional-input weak/strict
hardness, stated explicitly in Corollary 9.4.

The modular potential determines complete descent-count residues at every
fixed ordinal head. Exact entry comparisons and a terminating arithmetic
elimination proof connect those residues to actual canonical assignments.
The paper includes the full literal assignment, parsing policy, greedy
collapse evaluator, repaired scalar and norm proofs, source translation,
and actual-source hardness reduction.

One control preserves any prescribed finite prefix of the published example
and alters later values by less than twice the input factorial. This is an
existence result within the permitted control framework. It does not decide
the same all-ground problem for the unchanged displayed control or for its
unchanged factorial. It also does not prove equality hardness for functional
inputs or a full alternating first-order arithmetic theory.

The [structural companion](../16-persistent-marking-termination-ordering/README.md)
proves the separate termination-ordering result. Three retained companions
treat [the unchanged standard control](../18-standard-control-comparison/README.md),
[source expressivity and control sensitivity](../19-source-expressivity-and-control-sensitivity/README.md),
and [modular descent arithmetic](../20-controlled-descents-and-cartier-observers/README.md).
The final discussion and bibliography now locate these results. The
[consolidation guide](../COMPARISON-RESOLUTION-GUIDE.md) maps the earlier
six-paper collection to the five current accounts and explains their exact
dependencies.

## Build and review

Run `python3 build_pdf.py` here with Python 3 and a standard TeX Live or MiKTeX
installation. The script runs pdfLaTeX three times and downloads nothing.
All required sources are in this directory. Computer Modern and AMS fonts
are embedded. `SHA256SUMS` identifies the committed edition; a later rebuild
can change PDF metadata and hence its byte hash.

The PDF has no unresolved references or layout warnings. Every page was
visually inspected, with changed pages checked again after review corrections.
[VERIFICATION.json](VERIFICATION.json) pins the PDF and build observations.
The mathematical review is AI-assisted hand review. It is not independent
human verification, a Lean proof of the new decision theorem, or a priority
assessment. Existing checked formalization targets are preserved as recorded.
