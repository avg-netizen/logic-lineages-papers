module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairCodeTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBetaPairCode
def ActualExplicitPairCode : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    (OrdinaryArithmetic.betaFormula (firstCode x y) (secondCode x y) OrdinaryArithmetic.zeroTerm x ⊓
      OrdinaryArithmetic.betaFormula (firstCode x y) (secondCode x y)
        (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) y)))
def ActualPairCodeExistence : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula (pairExists x y)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairCodeTargets
