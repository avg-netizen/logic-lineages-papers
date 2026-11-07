module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationZeroRemainderTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof

def ActualZeroOrSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (r : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((arithmeticEmbedding.onFormula (r.equal OrdinaryArithmetic.zeroTerm)) ⊔
      existsOne (arithmeticEmbedding.onFormula
        ((r.relabel Sum.inl).equal
          (OrdinaryArithmetic.succTerm (.var (.inr (0 : Fin 1))))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationZeroRemainderTargets
