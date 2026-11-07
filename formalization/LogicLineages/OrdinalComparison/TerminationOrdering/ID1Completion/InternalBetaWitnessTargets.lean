module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalFiniteBlocks InternalBetaWitness
def ActualBetaMatrix : Prop :=
  ∀ (α : Type) (a b i r : OTerm α),
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r) =
    block (arithmeticEmbedding.onFormula (matrix a b i r))
def ActualBetaIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α)) (a b i r q d : OTerm α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equations a b i r q d))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r)))
def ActualBetaElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α)) (a b i r : OTerm α) (psi : Formula α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula a b i r))) →
  Nonempty (Derivation body (arithmeticEmbedding.onFormula (matrix a b i r) ::
    Gamma.map (fun p => p.relabel Sum.inl)) (psi.relabel Sum.inl)) →
  Nonempty (Derivation body Gamma psi)
def ActualBetaZero : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (b i : OTerm α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    (OrdinaryArithmetic.betaFormula OrdinaryArithmetic.zeroTerm b i OrdinaryArithmetic.zeroTerm)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessTargets
