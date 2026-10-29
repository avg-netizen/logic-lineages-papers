# Logic lineages papers

[![Pure R1 Lean verification](https://github.com/avg-netizen/logic-lineages-papers/actions/workflows/pure-r1-lean.yml/badge.svg?branch=main)](https://github.com/avg-netizen/logic-lineages-papers/actions/workflows/pure-r1-lean.yml)

Working manuscripts and a standalone calculator/formalization project from a research programme in mathematical logic. Their source questions were posed by the authors identified below. Each manuscript is independently buildable; the new comparison collection cites its included companions for shared proofs. No argument or build requires private vault documents or project conventions.

An incomplete [Lean formalization programme](FORMALIZATION.md) covers all fifteen
papers. Its target register and component statuses distinguish the existing
checked calculator from the many full paper targets still pending. Every
dependency absent from the standard libraries remains an explicit obligation.

| Paper | Source problem | Main result |
|---|---|---|
| [Scott complexity of countable abelian p-groups](01-scott-complexity-abelian-p-groups/README.md) · [PDF](01-scott-complexity-abelian-p-groups/paper.pdf) | Alvir–Csima–MacLean (2024), Questions 5.1–5.2; Gonzalez–Rossegger–Turetsky (2026), Question 1 | Exact reduced-group classification; all successor difference levels; no exact pure Sigma level, including nonreduced groups. |
| [Equality and universal comparison of positive exponential terms](02-exponential-comparison/README.md) · [PDF](02-exponential-comparison/paper.pdf) | Wilken–Weiermann (2012), effectiveness conjecture following Definition 2.8 | Depth-two universal comparison is undecidable; identity and one-variable comparison have decision procedures. |
| [Joint embedding for finite order forests](03-joint-embedding-finite-forests/README.md) · [PDF](03-joint-embedding-finite-forests/paper.pdf) | Gonzalez–Rossegger–Turetsky (2026), Question 2 | Decision by reduction to Carter's graph theorem; explicit width classification and negative certificates. |
| [Pure R1 ordinal and pattern calculator](04-pure-r1-calculator/README.md) · [Paper PDF](04-pure-r1-calculator/paper.pdf) | Carlson's pure first-order resemblance; Wilken's endpoint recursion | Standalone Python calculator/CLI, finite-pattern maps and enumeration, sharp expanded-tree output-size bound, and checked Lean semantic endpoint, arithmetic, finite-pattern and sharp norm proofs. |

The six-paper [Wilken–Weiermann comparison collection](COMPARISON-COLLECTION.md)
provides the full shared foundations and thematic proof accounts for a larger
body of work. Start with its foundations and guide, then read the relevant
companion. The full standard-control comparison problem with several ground
inputs remains open.

| Manuscript | Contents |
|---|---|
| [Foundations and guide](05-wilken-weiermann-foundations/README.md) · [PDF](05-wilken-weiermann-foundations/paper.pdf) | Original questions, canonical clauses, maximal predecessor, closed evaluator, complete counts and source translation. |
| [Gödel-T termination ordering](06-godel-t-termination-ordering/README.md) · [PDF](06-godel-t-termination-ordering/paper.pdf) | Exact finite comparator, type confinement, stability, literal rule orientation, ranked RPO restriction and Bachmann–Howard descending height. |
| [Collapse equality and one-variable comparison](07-collapse-equality-and-one-variable/README.md) · [PDF](07-collapse-equality-and-one-variable/paper.pdf) | Multivariate identity normal form; complete one-variable eventual-sign and finite-exception algorithms. |
| [Multivariate decidable fragments](08-multivariate-collapse-comparison/README.md) · [PDF](08-multivariate-collapse-comparison/paper.pdf) | Exact arithmetic hypotheses, finite and polynomial heads, internal-level-two source comparison, common-head, balanced and single-core classes. |
| [Actual-source expressivity](09-canonical-source-expressivity/README.md) · [PDF](09-canonical-source-expressivity/paper.pdf) | Boolean compiler, absolute and unit observations, ground-binder construction, entire head graphs, functional-input and perturbed-control hardness. |
| [Controlled descents and modular counts](10-collapse-descent-and-modular-counts/README.md) · [PDF](10-collapse-descent-and-modular-counts/paper.pdf) | Growing-budget partition transfer, linked source parameters, complete Cartier observer and exact actual residue-tuple period. |

The calculator project includes its own implementation, tests, explanatory paper,
public Lake configuration and [formalization coverage](04-pure-r1-calculator/FORMALIZATION.md).
The Lean development reconstructs Carlson's semantic endpoint characterization
for normal left inputs and arbitrary actual right ordinals, together with the
sharp expanded-tree size theorem. It uses standard Lean/Mathlib foundations;
Python execution is separately tested. See the project's verification record.

Five further [papers on differentiation, knowledge and computation](DIFFERENTIATION-KNOWLEDGE-AND-COMPUTATION.md)
give complete accounts of several separate source questions and restricted
decision results. Each is independent of the other papers and includes every
local proof it uses.

| Manuscript | Main result |
|---|---|
| [The domain of hyperreal differentiation is always proper](11-hyperreal-differentiation-domain/README.md) · [PDF](11-hyperreal-differentiation-domain/paper.pdf) | Universal properness for admissible idempotent ultrafilters; an excluded positive infinitesimal and failure of order convexity. |
| [A theorem which is not common knowledge](12-common-knowledge-necessitation/README.md) · [PDF](12-common-knowledge-necessitation/paper.pdf) | Negative answer to Gorbow's unrestricted KT common-knowledge necessitation question, selector classification and direct consistency. |
| [Deterministic and stochastic RL transformations](13-reinforcement-learning-transformations/README.md) · [PDF](13-reinforcement-learning-transformations/paper.pdf) | Complete four-framework classification under the printed ranking-preservation contract, with full positive and negative proofs. |
| [The exact computability of two prediction measures](14-complexity-of-prediction-measures/README.md) · [PDF](14-complexity-of-prediction-measures/paper.pdf) | Exact third-jump degree for the original Hibbard measure and a specified canonical all-total-function variant. |
| [Explicit differential-field constraint decisions](15-differential-field-constraint-decisions/README.md) · [PDF](15-differential-field-constraint-decisions/paper.pdf) | First-order and independent-spectrum decisions over Q; the full predicate and historical novelty remain outside the claims. |

Each bundle contains the canonical `paper.tex`, its PDF, a local `preamble.tex`, `build_pdf.py`, a source/dependency guide and a verification record. Published mathematical theorems are cited normally; their proofs and copyrighted source PDFs are not bundled. The papers give their local arguments in full, with introductions and examples.

Use `python3 build_pdf.py` inside a paper directory. The script uses Tectonic in cached-resource mode, or pdfLaTeX if Tectonic is unavailable. For a first Tectonic build on a new machine, `python3 build_pdf.py --online` permits missing TeX resources to be downloaded. Python uses only its standard library. Computer Modern is selected explicitly; the preparation checks inspect the actual embedded fonts.

The papers are AI-assisted hand-proof manuscripts for review; the calculator project additionally includes the specifically documented Lean proofs. Their existence here does not establish historical priority, independent mathematical verification or journal publication. The general graph algorithm belongs to Carter; general Scott-complexity exclusions belong to the cited literature. See the individual source guides for the division of work.
