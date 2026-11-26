# Original subtraction alignment

The exact original `InternalEqualityTest.subtract` recursion takes [index,seed]
and computes seed-index. No replacement subtraction, external semantic oracle,
new stage bound or changed graph AST is introduced.

InternalComplement eliminates the strict-order gap in the bounded disjunction,
uses paid internal diagonal subtraction at index+gap and graph functionality,
and handles equality with paid subtractSelf. The gap is object-language data,
not a metatheoretic natural.

InternalPredecessorAlignment uses the complement equality and the paid addition
successor laws to rewrite seed as index+succ(depth), then paid diagonal subtraction.
The explicit bound suc(index)<=seed is essential; saturated subtraction cannot
support this conclusion without it.

This does not prove previous-stage capacity, the all-raw cross-root coherence
invariant, typed Some-definedness or source stability. It pays one exact index
alignment prerequisite for those results. Targets must remain immutable after
preflight; the coordinator owns compiler and independent reviewer approval.
