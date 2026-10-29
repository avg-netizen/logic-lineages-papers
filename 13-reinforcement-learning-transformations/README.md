# Transformations between deterministic and stochastic RL frameworks

[Paper (PDF)](paper.pdf) · [Canonical TeX](paper.tex) · [Sources](SOURCES.md) · [Verification](VERIFICATION.md)

The paper classifies every pair of the four standard frameworks in Alexander–Pedersen's current transformation definition. With at least two actions, a transformation exists exactly when source agents are deterministic or target agents are stochastic. A singleton action alphabet admits none because image nontriviality fails.

The eight-page manuscript gives the positive construction, a finite deterministic separator, the full behavioral-mixture proof, and all negative cases. It also shows why the naturally composed maps may lose the definition's existential nontriviality witnesses and explains a distinct cross-environment obstruction. This is a full follow-up to [the earlier public counterexample](https://github.com/avg-netizen/alexander-open-problems-results/tree/main/05-rl-transformation-counterexample); all arguments needed here are included.

The classification permits noninjective agent maps and potentially noncomputable environment maps. It is not a practical policy-conversion algorithm or a classification for stronger notions of translation.

Build with `python3 build_pdf.py` here, using cached Tectonic resources or pdfLaTeX. `--online` permits missing resources on a new Tectonic installation. The paper uses Computer Modern.

AI-assisted hand-proof manuscript for review; no formal certificate or established priority claim.
