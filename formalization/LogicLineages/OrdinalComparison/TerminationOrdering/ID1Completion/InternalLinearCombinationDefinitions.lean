module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombination
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
abbrev OTerm (α : Type) := OrdinaryArithmetic.Term α
/-- Signed natural linear combination; all four coefficients are existentially bound. -/
def equation {α : Type} (a b d x y z w : OTerm α) : OrdinaryArithmetic.Formula α :=
  (OrdinaryArithmetic.addTerm (OrdinaryArithmetic.mulTerm x a) (OrdinaryArithmetic.mulTerm y b)).equal
    (OrdinaryArithmetic.addTerm d (OrdinaryArithmetic.addTerm
      (OrdinaryArithmetic.mulTerm z a) (OrdinaryArithmetic.mulTerm w b)))
def matrix {α : Type} (a b d : OTerm α) : OrdinaryArithmetic.Formula (α ⊕ Fin 4) :=
  equation (a.relabel Sum.inl) (b.relabel Sum.inl) (d.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
def combination {α : Type} (a b d : OTerm α) : OrdinaryArithmetic.Formula α :=
  OrdinaryArithmetic.existsFin (matrix a b d)
def positiveFamily {α : Type} (a b : OTerm α) : OrdinaryArithmetic.Formula (α ⊕ Fin 1) :=
  combination (a.relabel Sum.inl) (b.relabel Sum.inl) (OrdinaryArithmetic.succTerm (.var (.inr 0)))
def divides {α : Type} (d a : OTerm α) : OrdinaryArithmetic.Formula α :=
  OrdinaryArithmetic.existsFin
    ((a.relabel (Sum.inl : α → α ⊕ Fin 1)).equal
      (OrdinaryArithmetic.mulTerm (.var (.inr 0)) (d.relabel Sum.inl)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombination
