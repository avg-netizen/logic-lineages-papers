# Controlled Ordinal Descents, Restricted Partitions, and Finite Cartier Observers

**14-page explanatory manuscript, 17 November 2026.**
[Read the paper](paper.pdf) · [LaTeX source](paper.tex) · [Sources and scope](SOURCES.md)

The paper develops the independent modular arithmetic of norm-controlled
ordinal descents. It proves the exact predecessor and complete-count formulas,
a restricted-partition count for constant budgets, and a transfer theorem for
congruent growing budgets. For the unchanged standard control it derives a
genuine retained-prefix family whose cutoff and selected partition index are
linked by one entry parameter.

The finite numerator observer retains every coefficient over F_2. After an
explicit transient, a complete residue profile is closed under both binary
selectors and has an exact scalar output formula. On the linked inputs, a
primitive-root residue tuple has an exact unbounded period. The complete
state therefore has no uniform period bound along that family.

That full-state result does not prove nonperiodicity of the selected scalar
bit. A genuine ordinal-descent input is also distinguished from a typed-source
realization inside an arbitrary larger assignment. The paper is a rewritten,
self-contained account of entry 10, with the full-profile closure proof added.
Its finite algebra and descent checks are included under `checks/`; their
bounds and result counts are explicit and are not a proof of the general
theorems.

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
