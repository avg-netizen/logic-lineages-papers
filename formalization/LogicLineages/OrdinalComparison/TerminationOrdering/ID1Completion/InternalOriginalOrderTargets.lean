module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof

def ActualOriginalOrderEmbedding : Prop :=
  ∀ (α : Type) (s t : OrdinaryArithmetic.Term α),
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t) =
    existsOne (arithmeticEmbedding.onFormula
      ((OrdinaryArithmetic.addTerm (s.relabel Sum.inl)
        (OrdinaryArithmetic.succTerm (.var (.inr (0 : Fin 1))))).equal (t.relabel Sum.inl)))

def ActualOriginalOrderIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (s t w : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.addTerm s (OrdinaryArithmetic.succTerm w)).equal t))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t)))

def ActualOriginalOrderElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (s t : OrdinaryArithmetic.Term α) (psi : Formula α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t))) →
  Nonempty (Derivation body
    (arithmeticEmbedding.onFormula
      ((OrdinaryArithmetic.addTerm (s.relabel Sum.inl)
        (OrdinaryArithmetic.succTerm (.var (.inr (0 : Fin 1))))).equal (t.relabel Sum.inl)) ::
      Gamma.map weaken) (weaken psi)) →
  Nonempty (Derivation body Gamma psi)

def ActualOriginalOrderIrreflexivity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula t t)).not)

def ActualOriginalOrderTransitivity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t u : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t) ⊓
      arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula t u)).imp
      (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s u))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderTargets
