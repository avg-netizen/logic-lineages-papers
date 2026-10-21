# Joint embedding for finite order forests

[Full paper (PDF)](paper.pdf) · [Canonical TeX](paper.tex) · [Source guide](SOURCES.md) · [Checks](VERIFICATION.md)

The paper answers the finite forbidden-family forest question by an effective reduction to Carter's graph algorithm. It proves the comparability-graph transfer, classifies JEP for width-bounded forests exactly, explains negative certificates and constructs countable realizations of hereditary classes with JEP.

The source question is Question 2 of Gonzalez–Rossegger–Turetsky, arXiv:2606.15205v2. Carter supplies the general decision algorithm; this paper does not claim to invent or implement it. Embeddings preserve and reflect the order; roots, parents and meets are not named. The countable age construction alone does not imply a Scott-rank classification or first-order Vaught's conjecture.

Build with `python3 build_pdf.py` in this directory. Tectonic or pdfLaTeX is required; a new Tectonic installation can use `--online` to obtain TeX resources. No parent directory or private project file is required. The PDF uses Computer Modern with AMS mathematical symbols.

This is an AI-assisted working manuscript with hand proofs, without independent human review, a formal certificate or an established priority claim.
