module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairCode
open FirstOrder Language
open OrdinaryArithmetic
def twice {α : Type} (t : Term α) : Term α := addTerm t t
def secondCode {α : Type} (x y : Term α) : Term α := addTerm x y
def firstQuotient {α : Type} (y : Term α) : Term α := succTerm (twice (twice y))
def secondQuotient {α : Type} (y : Term α) : Term α := succTerm (twice y)
def firstCode {α : Type} (x y : Term α) : Term α :=
  addTerm (mulTerm (firstQuotient y) (succTerm (secondCode x y))) x
def matrix {α : Type} (x y : Term α) : OrdinaryArithmetic.Formula (α ⊕ Fin 2) :=
  betaFormula (.var (.inr 0)) (.var (.inr 1)) zeroTerm (x.relabel Sum.inl) ⊓
    betaFormula (.var (.inr 0)) (.var (.inr 1)) (succTerm zeroTerm) (y.relabel Sum.inl)
def pairExists {α : Type} (x y : Term α) : OrdinaryArithmetic.Formula α := existsFin (matrix x y)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairCode
