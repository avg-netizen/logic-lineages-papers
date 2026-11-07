module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
/-- Full unconditional target, not claimed by the preliminary supplier checks. -/
def ActualLeastNumber : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (p : OrdinaryArithmetic.Formula (α ⊕ Fin 1)),
  Nonempty (Derivation body [] ((existsOne (arithmeticEmbedding.onFormula p)).imp
    (existsOne (InternalLeastNumber.minimal p))))
def ActualRightSuccessorSplit : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s (OrdinaryArithmetic.succTerm t))).imp
      (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t) ⊔
        arithmeticEmbedding.onFormula (s.equal t))))
def ActualNothingBelowZero : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s OrdinaryArithmetic.zeroTerm)).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberTargets
