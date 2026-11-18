# Provenance and scope

This file preserves dated preparation records. The current comparison
organization is described in the [five-paper guide](COMPARISON-RESOLUTION-GUIDE.md).
Earlier counts and scope statements below describe their own editions.

## 21 October 2026: original papers and subsequent calculator addition

Prepared 21 October 2026 at the repository owner's request. The owner selected and directed the research programme. AI systems developed the working arguments, including user-supplied Pro reports and internal Codex assessments; Codex assembled these three manuscripts and their build files. No individual is assigned mathematical authorship merely by this preparation record.

Each directory contains a canonical TeX manuscript, its PDF, standalone build support, a source/dependency guide and an assembly-check record. The calculator directory added on 23 October 2026 also contains self-contained Python code/tests and pinned Lean source with explicit proof coverage. The papers require no private vault files or conventions. Established theorems are cited normally; their proofs and copyrighted source PDFs are not redistributed.

- **Scott complexity:** credits Alvir–Csima–MacLean's reduced-group analysis, general Scott-complexity restrictions of Alvir–Greenberg–Harrison-Trainor–Turetsky, Ulm classification, Zippin existence as stated by Calderoni–Thomas, and Gonzalez–Rossegger–Turetsky's earlier abstract existence results. The terminal-deletion and divisible-rank arguments are local hand-proof dependencies.
- **Exponential comparison:** imports MRDP and the specified Wilken–Weiermann syntax and norm estimates. The positive multiplication gadget, comparison reduction, normal forms and decision arguments are given in the paper.
- **Finite forests:** Carter supplies the general graph JEP algorithm. The manuscript proves the exact order/graph transfer and the explicit width classification; it does not claim an independent implementation of Carter's algorithm.

- **Pure R1 calculator:** Carlson supplies the semantic arithmetic characterization; Wilken supplies the displayed endpoint recursion. The software and exposition implement these known results. The paper and Lean development reconstruct the semantic endpoint characterization for normal left inputs and arbitrary actual right ordinals through explicit finite copies, forest capacity, endpoint obstructions and recursive uniqueness. The sharp expanded-tree bound and its all-size tower witnesses are formalized too. There are no added axioms or admitted proofs; the standard Lean/Mathlib foundations remain dependencies. Selected formula/finite-diagram constructions were adapted from the Alexander thesis formalization and checked locally. This does not certify Python execution or assert the global periodic extension beyond the calculator's range. The owner selected and directed this public addition; Codex and the three existing lanes prepared it.

The assembly checks establish that the PDFs build in isolation, use embedded Computer Modern fonts, and have no unresolved TeX references or layout warnings. They do not establish mathematical correctness. For those three manuscripts no proof-assistant verification is claimed. The calculator project's specifically documented Lean results are kernel-checked; no independent human review or historical priority is claimed for any bundle. The same-model or AI assessments in the research process are not described as independent verification.

These are full working manuscripts for review. They do not settle first-order Vaught's conjecture, the complete original termination-ordering target, or every algebraic back-and-forth problem mentioned in the source literature. The source guides and conclusions state the exact remaining scope.

This repository contains the three original logic-lineages papers and the standalone R1 calculator/formalization project. Alexander's dissertation Open Problem 3.2.1 and its paper remain in the separate [Alexander open-problems repository](https://github.com/avg-netizen/alexander-open-problems-results/tree/main/18-dissertation-problem-3-2-1).

## 28 October 2026: earlier comparison collection

The six-manuscript Wilken–Weiermann comparison collection was prepared on
28 October 2026 at the owner's request. A coordinating Codex author and two
additional Codex author lanes consolidated the earlier working mathematics
into a foundations paper and five thematic companions. Its new proofs are
printed within the collection; its historical origin metadata are not external
proof dependencies. Published assignment, path-order, arithmetic, undecidability
and ordinal-analysis theorems are credited in the respective bibliographies.
The scoped original-source bridge arguments are included in full.

The collection has 88 pages and 112 numbered theorem/lemma/proposition/corollary
statements. It includes a calibrated syntactic ordering, identity and one-input
decisions, multivariate positive classes, actual-source interpretation and
negative boundaries, and exact count/Cartier results. Its syntactic ordering
uses a separate ranked first-order embedding, rather than claiming every
native curried encoding has the same restriction. Functional-input hardness
and perturbed-control ground hardness retain their different domains. The
full unchanged-control, all-ground canonical comparison problem remains open.
These are AI-assisted hand-proof manuscripts; their clean builds and
collaborative reviews are not proof-assistant or independent human verification.
See [the collection guide](COMPARISON-COLLECTION.md) and its verification record.


## 17 November 2026: initial two-paper explanatory edition

At the owner's request, OpenAI Codex consolidated the new structural and
numerical results into [two companion papers](COMPARISON-RESOLUTION-GUIDE.md),
29 and 30 pages respectively. They supply their local proofs in full and use
ordinary published references. The six earlier sources, their checked
counterexamples, and their formalization targets are preserved. The new
structural definition uses persistent marking, and the numerical theorem
uses explicitly permitted controls; neither change is silently attributed
to the earlier formalized objects.

The edition includes the repaired weak scalar and unchanged-multiplier norm
proof, exact entry-domain and arithmetic-cancellation arguments, native
structural rank calibration, standalone LaTeX builds, PDF inspection and
per-bundle hashes. All 59 pages were visually reviewed. These checks are
AI-assisted hand review and document preparation, not independent human
verification, a completed formal port, or a historical priority assessment.
The existing formal target counts are unchanged.

## 17 November 2026: retained comparison material reorganized

At the owner's request, the useful material outside the two core papers was
reorganized into three companions:

- **Identities and Comparison for the Standard Ordinal Collapse** combines
  the older identity, one-variable and multivariate-fragment papers and
  retains the relevant source classes from the foundations paper: 37 pages.
- **Source Expressivity and Control Sensitivity of Ordinal Assignments**
  consolidates the remaining source constructions, observers, diagnostics,
  policy example and additive-one control-hardness theorem: 18 pages.
- **Controlled Ordinal Descents, Restricted Partitions, and Finite Cartier
  Observers** rewrites the independent modular material with local numerical
  foundations and a complete residue-profile construction: 14 pages.

The main numerical paper remains 30 pages after adding companion references
and Corollary 9.4, which explicitly retains functional-input weak/strict
hardness for the unchanged standard control. Its reduction proof and the
29-page structural paper are unchanged. The five current papers total
128 pages; the retained companions account for 69 of them.

The standard-control rewrite replaces a false strict range lower bound by
the sufficient nonstrict estimate, supplies the finite graph-domain case
split, and retains shared certificates and original variables. The source
rewrite corrects the reserve transport for arbitrary admitted parsing
policies, closes all ground names in a separate auxiliary carrier, and
states the common-unit convention. The modular rewrite includes every pole
and both selector transitions, distinguishes adjacent control inputs from
the norm orbit, and restricts its finite-cycle assertion to the finite-field
setting. Its residue-tuple period is not promoted to scalar nonperiodicity.

The printed arithmetic supplier in A. S. Snyatkov's 2008 paper was checked
against its institutional primary PDF, including the separate fixed-seed
hyperfunction condition. The companion verifies these hypotheses for its
literal hierarchy. Published work and companion proofs are cited by normal
bibliographic titles and public links. No copyrighted source PDF is included.

All 99 pages in the four new or updated PDFs were visually inspected. Each
bundle has a clean standalone build, embedded fonts, an exact PDF record,
page-review evidence and checksums. The modular bundle also includes finite
algebra and descent checks with explicit ranges. These are document and
bounded-interface checks, alongside AI-assisted hand review; they are not a
formal verification of the assembled collection or independent human review.

The earlier sources, PDFs, correction records, obstruction and formalization
files are preserved. Their entry pages now identify the current homes. The
formal register remains 170 checked, 2 inherited and 17 pending out of 189;
no fresh Lean build or changed target status is claimed. The selected-control
decision theorem, unchanged-control positive fragments and control-sensitivity
hardness concern the distinct scopes stated in the collection guide.
