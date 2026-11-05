# Multivariate decidable fragments of canonical comparison

[Paper PDF](paper.pdf) · [TeX](paper.tex) · [Source guide](SOURCES.md)

The paper gives exact decision procedures for finite-coefficient canonical
sources, finite-degree polynomial collapse expressions, nested common-head
sums, balanced heterogeneous layers, and arbitrary single-core rows. It
includes all counters, finite exceptions, shared-variable guards, termination
measures, and the actual-source internal-type-level-two consumer.

The full all-ground canonical comparison problem remains open. The polynomial
arithmetic result is a closed existential decision theorem, not full
first-order quantifier elimination. At arbitrary fixed heads the explicitly
stated comparison certificates are required.

Run `python3 build_pdf.py` to build with cached Tectonic resources. The local
TeX inputs use Computer Modern explicitly. Named mathematical dependencies
are ordinary published sources and included companion manuscripts.

## Formalization

The finite-coefficient source comparison theorem (`thm:finite-source`) is checked in Lean, including genuine WW admissible substitutions, weak/WW-strict/equality decisions, exact computable source admission and recursor-free inclusion without internal-type bounds. The paper remains in progress; full first-order BASE and unrestricted canonical comparison are separate. See the [accepted checkpoint](../formalization/verification/cumulative-continuation-2026-11-05/finite-source-comparison/STATUS.md) and [source completion audit](../formalization/audits/FINITE-SOURCE-COMPLETION-2026-11-05.md).
