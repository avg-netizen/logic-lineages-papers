# Preparation checks

Checked 21 October 2026. The PDF has **9 pages**.

- The canonical manuscript builds with Tectonic 0.17.0 using cached resources and untrusted mode.
- An isolated build passed after copying only paper.tex, preamble.tex and build_pdf.py to a temporary directory outside the vault. No repository parent files were present.
- The final TeX log has no unresolved references or citations, missing characters, overfull/underfull boxes or other warnings.
- PDF font inspection confirms embedded Computer Modern fonts, with AMS symbols where used. No DejaVu or Latin Modern fallback appears.
- Local labels and proof-environment balance were checked; native proof environments supply visible QED endings. Representative PDF pages were visually inspected.
- Source and PDF hashes, the font list and the build details are recorded in [VERIFICATION.json](VERIFICATION.json).

These checks concern document assembly and reproducibility. They are not an independent mathematical audit, a proof-assistant certificate, or a priority search. Published theorem dependencies are listed in [SOURCES.md](SOURCES.md).
