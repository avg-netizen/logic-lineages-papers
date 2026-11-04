module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransformsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperators
open PositiveArithmeticOperators PositiveArithmeticTransforms

def taggedBranch (odd : Bool) (body : Positive (Fin 2)) : Positive (Fin 2) :=
  .all (.guarded
    (((.var (.inl (1 : Fin 2)) : OrdinaryArithmetic.Term (Fin 2 ⊕ Fin 1))).equal
      (tagTerm odd (.var (.inr (0 : Fin 1)))))
    (relabel ![.inl (0 : Fin 2),.inr (0 : Fin 1)] (tagPredicate odd body)))

def combinedOperator (scalar multiset : Positive (Fin 2)) : Positive (Fin 2) :=
  .conj (taggedBranch false scalar) (taggedBranch true multiset)

end LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperators
