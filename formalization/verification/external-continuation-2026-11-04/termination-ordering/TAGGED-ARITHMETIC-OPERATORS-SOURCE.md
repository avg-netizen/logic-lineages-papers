# Disjoint tagged combination of actual positive source operators

Paper06 lines569–571 combines two separate unnested operators through disjoint numeric tags. This component constructs literal positive syntax for both branches: for every x, z=2*x implies the scalar body with predicate arguments tagged even; for every x, z=2*x+1 implies the multiset body with predicate arguments tagged odd. Both clauses are conjoined. The arithmetic tag equality has no inductive predicate.

The natural numbers partition uniquely into these tags. Exact branch isolation preserves the original carrier/edge guards and ensures that scalar successors query only the even predicate slice, while multiset successors query only the odd slice. The original positive R and direct DM remain source-to-successor relations; no cross-sort edge is introduced.

Targets establish tag partition, actual syntax semantics, standard-N monotonicity and the combined instantiated source operators. Positivity follows from the accepted grammar. These are not fixed-point existence, closure/leastness axioms, ID1 derivability, accessibility or well-foundedness theorems.
