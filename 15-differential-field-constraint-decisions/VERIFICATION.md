# Verification and scope

Prepared 28 October 2026. The canonical manuscript compiles with cached-resource Tectonic; no network download was needed. A second build in a temporary directory containing only paper.tex, preamble.tex and build_pdf.py also passed, with identical extracted PDF text and page count.

- PDF: 8 pages; approximately 3476 extracted words.
- Numbered theorem-like statements: 2 theorems, 5 lemmas, 1 proposition, 1 corollary.
- All embedded fonts are Computer Modern or AMS mathematical fonts.
- No unresolved references/citations, missing-character warnings, overfull boxes or other compiler warnings.
- The manuscript's TeX inputs are local; no private research path or problem identifier occurs in its text.
- Sampled visual inspection: page(s) 6.

[VERIFICATION.json](VERIFICATION.json) records exact source and PDF hashes, font names and isolated-build results. The aggregate report is [here](../FIVE-PAPER-VERIFICATION.json). These are document and integrity checks. The mathematics consists of hand proofs with imported same-model reviews and an author consistency pass; compilation is not mathematical certification, a new independent audit or a priority determination.

Rebuild with `python3 build_pdf.py`. Inspect the PDF with `pdfinfo paper.pdf`, `pdffonts paper.pdf` and `pdftotext paper.pdf -`. On a new TeX installation, the build script's `--online` option permits missing resources to be fetched.
