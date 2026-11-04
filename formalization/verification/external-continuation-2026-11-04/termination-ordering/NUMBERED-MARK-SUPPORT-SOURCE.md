# Successful mark support and one-way occurrence replacement support

Draft for review; no proof/export. Actual primitive marking/Mul support supplier for paper 06 auxiliary reduction.

finiteMark success preserves support iff for arbitrary typed predicate P. Ordinary marking retains base and adds empty extras; lambda recurses under liftPredicate P. Variable/application/bottom/already-numbered branches cannot succeed. No failure reflection or unconditional Option statement is asserted. PrimitiveMark inherits this iff from its literal successful finiteMark witness.

PrimitiveMultiset support is only forward. The actual kept/removed/inserted witness, source/target permutations, nonempty removal and inserted-occurrence dominators are unchanged. Kept occurrences inherit source support; every inserted occurrence inherits support from its removed dominator via PrimitiveMark. Dominator reuse and multiplicities are allowed exactly as in the relation.

Reverse counterexample: take a context containing a variable v with P v false, source=[packed(var v)], kept=[], removed=source, inserted=[], target=[]. Both permutations and nonempty removal hold, and the inserted-dominator condition is vacuous. Target is supported but source is not. Thus no reverse multiset statement is claimed.

No full WindowStep support preservation, image closure, Acc/C stability, ID1 or export. Prior accepted bytes unchanged.
