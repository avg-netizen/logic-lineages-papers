module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaWitnessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCongruenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
/-- The literal original beta relation supplies the literal modular relation. -/
def ActualBetaCongruence : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (c b i r : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula
    (OrdinaryArithmetic.betaFormula c b i r)).imp (arithmeticEmbedding.onFormula
    (InternalModularArithmetic.congruent c r (InternalBetaWitness.modulus b i)))))
/-- Bounded residues in the genuine two-offset congruence are equal internally. -/
def ActualBoundedCongruenceEquality : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (r s m : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (((arithmeticEmbedding.onFormula
    (InternalModularArithmetic.congruent r s m)) ⊓
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula r m) ⊓
     arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s m))).imp
    (arithmeticEmbedding.onFormula (r.equal s))))
/-- Congruence and the original residue bound imply the unchanged beta formula. -/
def ActualBoundedCongruenceBeta : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (c b i r : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (((arithmeticEmbedding.onFormula
    (InternalModularArithmetic.congruent c r (InternalBetaWitness.modulus b i))) ⊓
    arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula r (InternalBetaWitness.modulus b i))).imp
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.betaFormula c b i r))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCongruenceTargets
