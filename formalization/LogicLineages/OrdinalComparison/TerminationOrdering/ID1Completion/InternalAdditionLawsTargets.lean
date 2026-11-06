module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus

def ActualAdditionLeftZero : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.addTerm OrdinaryArithmetic.zeroTerm t).equal t)))

def ActualAdditionLeftSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.addTerm (OrdinaryArithmetic.succTerm s) t).equal
      (OrdinaryArithmetic.succTerm (OrdinaryArithmetic.addTerm s t)))))

def ActualAdditionAssociativity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t u : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.addTerm (OrdinaryArithmetic.addTerm s t) u).equal
      (OrdinaryArithmetic.addTerm s (OrdinaryArithmetic.addTerm t u)))))

def ActualAdditionRightCancellation : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t u : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    (((OrdinaryArithmetic.addTerm s u).equal (OrdinaryArithmetic.addTerm t u)).imp (s.equal t))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsTargets
