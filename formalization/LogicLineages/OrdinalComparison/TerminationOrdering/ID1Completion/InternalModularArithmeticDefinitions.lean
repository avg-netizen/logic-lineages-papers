module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmetic
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
abbrev OTerm (α : Type) := OrdinaryArithmetic.Term α
def equation {α : Type} (a b m q p : OTerm α) : OrdinaryArithmetic.Formula α :=
  (OrdinaryArithmetic.addTerm a (OrdinaryArithmetic.mulTerm q m)).equal
    (OrdinaryArithmetic.addTerm b (OrdinaryArithmetic.mulTerm p m))
def matrix {α : Type} (a b m : OTerm α) : OrdinaryArithmetic.Formula (α ⊕ Fin 2) :=
  equation (a.relabel Sum.inl) (b.relabel Sum.inl) (m.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))
def congruent {α : Type} (a b m : OTerm α) : OrdinaryArithmetic.Formula α :=
  OrdinaryArithmetic.existsFin (matrix a b m)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmetic
