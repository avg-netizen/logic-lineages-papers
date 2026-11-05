# Exact functional-hardness assembly

The comparator is the unchanged `HardnessTargets.FullFunctionalHardness`:
strict and weak level-two source comparison undecidability, both actual
level-two finite-query reductions, and both level-three single-query
reductions. Its source domain retains every context of level-at-most-one
types, the stated internal term-level bounds, and the original admissible
substitution semantics.

For each fixed strictness flag, the hypothetical decision program is applied
only to the concrete ground-query codes returned by the already checked
finite-query reduction. Each use of its correctness theorem consumes the
actual ground-query witness, context-type bound and both term bounds. No
meaning or correctness is required on malformed or out-of-domain codes.

Finite Boolean conjunction returns true precisely when every query's universal
comparison holds. The reduction equates this with polynomial-system
UNsatisfiability, not satisfiability. Computable predicate complementation then
produces a hypothetical satisfiability decider, contradicted by the separately
proved genuine polynomial-system undecidability theorem. Strict and weak
comparison relations are never identified with one another by complementation.
Empty lists and repeated codes retain ordinary finite-conjunction semantics.

The final assembly uses actual proved reductions, not fields or assumptions
standing in for the required effectiveness or undecidability suppliers.
Independent review is required before adoption or publication.
