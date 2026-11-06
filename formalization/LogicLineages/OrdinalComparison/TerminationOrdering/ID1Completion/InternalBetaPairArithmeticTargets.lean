module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairArithmeticTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBetaPairCode
open OrdinaryArithmetic
/-- Original syntactic arithmetic equality, in every original derivation context. -/
def ActualPairEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (InternalCalculus.Formula α))
    (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula
    ((firstCode x y).equal
      (addTerm (mulTerm (secondQuotient y) (succTerm (twice (secondCode x y)))) y))))
def ActualOneMultiplication : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (InternalCalculus.Formula α))
    (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula
    ((mulTerm (succTerm zeroTerm) t).equal t)))
def ActualTwoMultiplication : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (InternalCalculus.Formula α))
    (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula
    ((mulTerm (succTerm (succTerm zeroTerm)) t).equal (twice t))))
def ActualBoundEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (InternalCalculus.Formula α))
    (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula
    ((addTerm y (succTerm (addTerm (twice x) y))).equal
      (succTerm (twice (secondCode x y))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairArithmeticTargets
