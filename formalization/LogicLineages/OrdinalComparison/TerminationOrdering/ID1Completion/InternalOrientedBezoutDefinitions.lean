module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutCRTDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutExistenceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezout
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
abbrev OTerm (α : Type) := OrdinaryArithmetic.Term α
open OrdinaryArithmetic (addTerm mulTerm succTerm)
def leftCoefficient {α : Type} (b x z w : OTerm α) : OTerm α :=
  addTerm (addTerm z (mulTerm x b)) (mulTerm w (succTerm b))
def rightCoefficient {α : Type} (a x y w : OTerm α) : OTerm α :=
  addTerm (addTerm (mulTerm x (succTerm a)) y) (mulTerm w a)
def matrix {α : Type} (a b : OTerm α) : OrdinaryArithmetic.Formula (α ⊕ Fin 2) :=
  InternalBezoutCRT.certificate ((succTerm a).relabel Sum.inl) (b.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))
def oriented {α : Type} (a b : OTerm α) : OrdinaryArithmetic.Formula α :=
  OrdinaryArithmetic.existsFin (matrix a b)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezout
