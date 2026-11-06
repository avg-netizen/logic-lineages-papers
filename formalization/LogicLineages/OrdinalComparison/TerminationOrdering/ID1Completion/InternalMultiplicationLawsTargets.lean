module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
def ActualMultiplicationLeftZero : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.mulTerm OrdinaryArithmetic.zeroTerm t).equal OrdinaryArithmetic.zeroTerm)))
def ActualMultiplicationDistributivity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t u : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.mulTerm s (OrdinaryArithmetic.addTerm t u)).equal
      (OrdinaryArithmetic.addTerm (OrdinaryArithmetic.mulTerm s t) (OrdinaryArithmetic.mulTerm s u)))))
def ActualMultiplicationAssociativity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t u : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.mulTerm (OrdinaryArithmetic.mulTerm s t) u).equal
      (OrdinaryArithmetic.mulTerm s (OrdinaryArithmetic.mulTerm t u)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsTargets
