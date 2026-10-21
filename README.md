# Logic lineages papers

Three full working manuscripts from a research programme in mathematical logic. Their source questions were posed by the authors identified below. Each directory is independently buildable and has no dependency on private vault documents or project conventions.

| Paper | Source problem | Main result |
|---|---|---|
| [Scott complexity of countable abelian p-groups](01-scott-complexity-abelian-p-groups/README.md) · [PDF](01-scott-complexity-abelian-p-groups/paper.pdf) | Alvir–Csima–MacLean (2024), Questions 5.1–5.2; Gonzalez–Rossegger–Turetsky (2026), Question 1 | Exact reduced-group classification; all successor difference levels; no exact pure Sigma level, including nonreduced groups. |
| [Equality and universal comparison of positive exponential terms](02-exponential-comparison/README.md) · [PDF](02-exponential-comparison/paper.pdf) | Wilken–Weiermann (2012), effectiveness conjecture following Definition 2.8 | Depth-two universal comparison is undecidable; identity and one-variable comparison have decision procedures. |
| [Joint embedding for finite order forests](03-joint-embedding-finite-forests/README.md) · [PDF](03-joint-embedding-finite-forests/paper.pdf) | Gonzalez–Rossegger–Turetsky (2026), Question 2 | Decision by reduction to Carter's graph theorem; explicit width classification and negative certificates. |

Each bundle contains the canonical `paper.tex`, its PDF, a local `preamble.tex`, `build_pdf.py`, a source/dependency guide and a verification record. Published mathematical theorems are cited normally; their proofs and copyrighted source PDFs are not bundled. The papers give their local arguments in full, with introductions and examples.

Use `python3 build_pdf.py` inside a paper directory. The script uses Tectonic in cached-resource mode, or pdfLaTeX if Tectonic is unavailable. For a first Tectonic build on a new machine, `python3 build_pdf.py --online` permits missing TeX resources to be downloaded. Python uses only its standard library. Computer Modern is selected explicitly; the preparation checks inspect the actual embedded fonts.

These are AI-assisted hand-proof manuscripts for review. Their existence here does not establish historical priority, independent mathematical verification or journal publication. The general graph algorithm belongs to Carter; general Scott-complexity exclusions belong to the cited literature. See the individual source guides for the division of work.
