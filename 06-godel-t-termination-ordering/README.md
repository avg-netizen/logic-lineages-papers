# A type-confined termination ordering for Gödel's T

Read [paper.pdf](paper.pdf). The canonical source is [paper.tex](paper.tex).

The paper constructs a decidable syntactic ordering, proves stability under
typed substitution and contexts, orients every original T reduction, and
identifies its descending height as Bachmann–Howard. Its first-order
restriction is exactly multiset RPO on a separately ranked finite ground
signature. This is distinct from curried native constants and from comparing
the numerical Wilken–Weiermann canonical assignments.

The exposition develops the recursive relation before its finite comparator,
then explains confinement, reduction-rule derivations, the finite-type ID1
upper argument, and the native-recursion iterator supplying the lower family.
It includes the original-spine application counterexample and a worked ranked
comparison.

All new proof arguments appear in the paper. Published background is cited
conventionally; the included foundations and expressivity manuscripts are
linked for the broader numerical problem. The bibliography does not cite
private research notes as proof suppliers.

Build with `python3 build_pdf.py`. This defaults to cached Tectonic resources;
`--online` permits resource downloads. A standard pdfLaTeX installation is
also supported. The local preamble uses Computer Modern and standard AMS
mathematical fonts.

[SOURCES.md](SOURCES.md) and [PROVENANCE.json](PROVENANCE.json) record editorial
origins. [VALIDATION.md](VALIDATION.md) records the build and document checks.
This is a hand-proof working manuscript, not a Lean formalization or a claim
of independent mathematical certification.
