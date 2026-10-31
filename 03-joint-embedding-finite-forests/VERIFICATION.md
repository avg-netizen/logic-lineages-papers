# Preparation checks

Checked 30 October 2026. The PDF has **9 pages** and 11 proof environments.

- The canonical manuscript builds with Tectonic 0.17.0 using cached resources and untrusted mode.
- An isolated build passed after copying only paper.tex, preamble.tex, decision.tex and build_pdf.py to a temporary directory outside the vault. No repository parent files were present.
- The final TeX log has no unresolved references or citations, missing characters, overfull/underfull boxes or other warnings.
- PDF font inspection confirms embedded Computer Modern fonts, with AMS symbols where used. No DejaVu or Latin Modern fallback appears.
- Local labels and proof-environment balance were checked; native proof environments supply visible QED endings. The technical page containing the full state-set and Parikh correspondence was rendered and visually inspected.
- Source and PDF hashes, the font list and the build details are recorded in [VERIFICATION.json](VERIFICATION.json).

The decision proof has received complete Codex author/root review and a separate canonical integration check, using the same model. Its dependencies are the independent ranked-tree ideal-decomposition and effective Parikh theorems, with the graph-image and inclusion arguments supplied in full. The [integration receipt](repair/decision/CANONICAL-INTEGRATION-REVIEW.json) identifies the checked files.

Two bounded semantic controls passed: 93,898 literal restrictions on 1,619 binary parses, and 10,817 exact state-set comparisons against 75,257 direct parse evaluations. The latter exhausts every pair of two-state transition tables through five leaves and adds three three-state examples through six leaves. Source hashes and the fixed resource bounds are included in the reports under [repair/cotree](repair/cotree/README.txt).

The full decision algorithm has not been implemented or formalized. These records do not constitute independent human review or a priority search. Existing Lean component results retain their separately recorded scope; this repair adds no kernel-checked target. Published dependencies are listed in [SOURCES.md](SOURCES.md).
