# Paper 16 principal theorem: items (1)–(5) only

Printed anchor: `16-persistent-marking-termination-ordering/paper.tex:96–114`. All five supporting clauses concern the same existing `ConfinedPair.Weak / Strict` (typed, ordinary endpoint domain and support inclusion).

1. The actual two `confinedBits` decide the two relations on every finite ordinary typed pair (#416).
2. Weak reflexivity and transitivity, strict transitivity and inclusion in weak, and `Weak;Strict` and `Strict;Weak` in their respective directions (#178). Full descending strict well-foundedness is already checked on the original symbolic expressions (#489); the relation to which Lean applies `WellFounded` has the smaller term first.
3. Both relations are preserved by original one-hole typed `fill` and ordinary, type-preserving capture-avoiding `freeSub` (#178), not just on closed or ranked terms. Context binders intentionally may bind free occurrences in the hole; that is distinct from capture avoidance in substitution.
4. Exact original beta, D0, DS, R0, RS and their closure under typed contexts and ordinary substitutions (#193).
5. On actual first-order F-terms (including ground-variable patterns), an iff between the strict confined relation and multiset recursive path order with the chosen signature precedence (#406).

The exact root combines existing evidence without a new ordering, decision input restriction, or any ordinal rank import. This is supporting evidence only: item (6), individual Bachmann–Howard bounds and exact height, is not asserted and no numbered theorem is promoted.
