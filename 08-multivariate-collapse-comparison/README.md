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

The finite-coefficient source comparison theorem (`thm:finite-source`) is checked in Lean, including genuine WW admissible substitutions, weak/WW-strict/equality decisions, exact computable source admission and recursor-free inclusion without internal-type bounds. The paper remains in progress; unrestricted canonical comparison remains separate. See the [accepted checkpoint](../formalization/verification/cumulative-continuation-2026-11-05/finite-source-comparison/STATUS.md) and [source completion audit](../formalization/audits/FINITE-SOURCE-COMPLETION-2026-11-05.md).

The complete first-order arithmetic supplier (`thm:snyatkov`) is now checked for
the exact source f(n)=F5(n+100), including arbitrary quantified original sentences
and an explicit total computable decision procedure. See the
[root adoption](../formalization/verification/local-six-sol-2026-11-12/ROOT-SNYATKOV-ADOPTION.json).
The full common-head (`thm:common`) and balanced (`thm:balanced`) comparison theorems are also checked, including exact free variables, effective pointwise compilers and arbitrary certified first-order decisions. See the [consumer adoption](../formalization/verification/local-six-sol-2026-11-12/ROOT-COMMON-BALANCED-ADOPTION.json).

The existing full original internal-level-two source comparison theorem
(`thm:leveltwo`) has also been revalidated and adopted at its unchanged complete
scope; see [the source review](../formalization/verification/local-six-sol-2026-11-12/ROOT-LEVELTWO-ADOPTION.json).
All numbered statements of this paper are now registered as checked. This does
not assert unrestricted canonical comparison beyond the stated source classes.
