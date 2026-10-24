# Sources and scope

The calculator implements a published pure-R1 endpoint recursion. Its source
questions, implementation checks and formal proof coverage have different roles.

| Source | What the package uses |
|---|---|
| Timothy J. Carlson, *Ordinal arithmetic and Sigma1-elementarity*, Archive for Mathematical Logic 38 (1999), 449–460, especially Definition 2.3 and Theorem 2.5. [Author manuscript](https://people.math.osu.edu/carlson.6/research/oase.pdf). | The arithmetic characterization of pure resemblance and its interval endpoints. The relevant semantic characterization is formally reconstructed here through finite induced copies and weighted forests; it is not a supplied Lean premise. The global periodic extension is outside the evaluator. |
| Gunnar Wilken, *Pure Sigma2-elementarity beyond the core*, Annals of Pure and Applied Logic 172 (2021), 103001; [arXiv version 5](https://arxiv.org/abs/1710.01870v5), Proposition 1.1 on page 2. | The explicit endpoint recursion below epsilon zero, in expanded principal-summand form. Using this introduction does not implement the paper's full R2 analysis. |
| Gunnar Wilken, *Pure patterns of order 2*, Annals of Pure and Applied Logic 169 (2018), 54–82. [Preprint](https://arxiv.org/abs/1608.08421). | Context for existing marked order-two notation results; these are not new results of this calculator. |
| Timothy J. Carlson, *Generalizing Kruskal's theorem to pairs of cohabitating trees*, author manuscript dated 6 October 2008, section 5; [published version](https://doi.org/10.1007/s00153-015-0457-4), Archive for Mathematical Logic 55 (2016), 37–48. | Motivation from minimal-cover order types. The conjecture passage is in the earlier author manuscript and omitted from the final journal body. It is not an algorithm dependency. |
| [Mathlib4 at revision 360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56](https://github.com/leanprover-community/mathlib4/tree/360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56), especially `Mathlib/SetTheory/Ordinal/Notation.lean`. | ONote/NONote arithmetic and its existing ordinal-denotation theorems. This package imports public dependencies rather than redistributing their source or altering their axioms. |

The compressed algorithm is explained in the paper. The expanded-tree quadratic
bound and its matching tower family are proved there, without a historical
priority claim. Finite pattern conditions use strict relation tables with
implicit reflexivity and a fixed linear order. Increasing coverings preserve
positive relation atoms; induced embeddings also reflect them. A marker is
optional and never silently identified with the maximum.

The Python tests check a separately expanded recurrence, independent ordinal
addition, malformed inputs and finite map cases. Kernel-checked Lean proofs
have their own [coverage guide](FORMALIZATION.md). Finite tests are execution evidence. The semantic endpoint characterization
and sharp expanded-tree bound have their own general Lean proofs; these do not
certify the Python interpreter. The [reuse guide](REUSE.md) credits selected
formula and finite-diagram constructions from the Alexander thesis development.

This is an independently usable implementation and exposition prepared from a
research prototype first developed on 18 October 2026. The repository owner
requested and directed its preparation; AI assistants developed the package,
formalization and manuscript. No individual is assigned mathematical authorship
merely by this preparation record. No copyrighted paper PDFs or private research
documents are included.
