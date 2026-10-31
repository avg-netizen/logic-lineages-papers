# The Wilken–Weiermann comparison collection

These six working manuscripts explain and prove the established parts of a
research programme around Wilken–Weiermann's ordinal assignments to Gödel's T.
They are organized by mathematical mechanism, rather than by the order in
which the research was done. The original paper is the 2012 revised LMCS
article, *Derivation lengths classification of Gödel's T extending Howard's
assignment*.

The first manuscript explains the problem and supplies the shared foundations.
The five companions contain the full local arguments for the thematic results.
Published theorems remain conventional literature references; the collection
does not reprove the background ordinal analyses or a published arithmetic
decision procedure. New bridge arguments are printed here. No unavailable
research note is a proof dependency.

| Read | Manuscript | Role |
|---|---|---|
| First | [Foundations and guide](05-wilken-weiermann-foundations/paper.pdf) | Defines the source calculus, canonical assignment and remaining problem; proves the evaluator, counts and source invariant. |
| Independently | [Termination ordering](06-godel-t-termination-ordering/paper.pdf) | A syntactic ordering, its comparator, stability and height; a different contract from numerical assignment comparison. |
| After foundations | [Equality and one variable](07-collapse-equality-and-one-variable/paper.pdf) | Identity separation, finite zeros, principal kernels and a complete eventual-sign algorithm. |
| After foundations | [Descent and modular counts](10-collapse-descent-and-modular-counts/paper.pdf) | Partition congruences, moving-prefix counts and full-state versus scalar observations. |
| With the partition-transfer theorem | [Multivariate comparison](08-multivariate-collapse-comparison/paper.pdf) | Positive decision classes, ranked cancellation and source consumers. |
| After foundations | [Actual-source expressivity](09-canonical-source-expressivity/paper.pdf) | Arithmetic interpretation, source construction and precisely scoped negative boundaries. |

At theorem level the dependencies are acyclic. The shared foundation does not
use its later overview of the companions to prove its foundational results.
The multivariate manuscript imports the counting paper's partition-transfer
theorem for counter residues. The counting paper proves its own residue
envelopes and transfer theorem, using the foundation for growth and the
predecessor operation. Its later references to expressivity describe context,
not premises of those proofs. The syntactic ordering's background comes from
the cited Kop, Pohlers and Simmons results, with the new interpretation and
finite algorithm proved in its own paper.

## The main scope distinctions

- A stable syntactic termination ordering is different from comparing the
  particular canonical numerical assignment. A ranked ground node is different
  from a curried native case functional.
- Exact source comparison uses the explicit binary expansion and padding
  convention in the foundations. Its Appendix A proves domain and norm
  preservation for every fixed admissible policy; values of whole source
  assignments can differ between policies.
- Universal identity is decided in several variables. Existential solution
  of simultaneous nonidentity equations is a different question.
- One shared ground input is decided, even at arbitrary internal types.
  Two separately named inputs are two independent variables.
- Several positive multivariate classes are decided. The full all-ground
  standard-control comparison problem with unrestricted internal types remains
  open.
- Functional-input hardness leaves the control unchanged; ground-input
  control-sensitivity hardness changes it. Neither settles that remaining
  all-ground, unchanged-control problem.
- Complete-count attainment for supplied actual source heads is a necessary
  arithmetic question. An isolated intermediate partition coefficient has not
  been proved equivalent to full comparison.
- The exact unbounded Cartier residue-tuple period is a full-state statement.
  It does not prove nonperiodicity or hardness of the selected scalar bit.

## Files and verification

Every directory includes TeX inputs, PDF, a local build script, a source guide
and provenance information. Run `python3 build_pdf.py` inside a directory.
Tectonic is used without network access by default; `--online` permits missing
resources on a new installation. pdfLaTeX is the alternative. Font selection
is explicit Computer Modern, with AMS mathematical symbols.

The collection's [verification record](COMPARISON-VERIFICATION.md) reports
isolated builds, references, links, embedded fonts and source hashes. Those
checks concern reproducibility and document consistency. They are not a
formal mathematical verification. The proofs received collaborative AI review;
no independent human audit, established novelty or journal acceptance is
claimed. The separate formalization register records checked components;
these six complete manuscripts and the source repair are not claimed to be
fully Lean verified.
