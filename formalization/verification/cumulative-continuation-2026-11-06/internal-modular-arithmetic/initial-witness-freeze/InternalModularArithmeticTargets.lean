module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalFiniteBlocks InternalModularArithmetic
abbrev add {α : Type} := @OrdinaryArithmetic.addTerm α
abbrev mul {α : Type} := @OrdinaryArithmetic.mulTerm α
def ActualMatrix : Prop :=
  ∀ (α : Type) (a b m : OTerm α), arithmeticEmbedding.onFormula (congruent a b m) =
    block (arithmeticEmbedding.onFormula (matrix a b m))
def ActualIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α)) (a b m q p : OTerm α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation a b m q p))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (congruent a b m)))
def ActualElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α)) (a b m : OTerm α) (psi : Formula α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (congruent a b m))) →
  Nonempty (Derivation body (arithmeticEmbedding.onFormula (matrix a b m) ::
    Gamma.map (fun p => p.relabel Sum.inl)) (psi.relabel Sum.inl)) →
  Nonempty (Derivation body Gamma psi)
def ActualReflexivity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a m : OTerm α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula (congruent a a m)))
def ActualWitnessSymmetry : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α)) (a b m q p : OTerm α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation a b m q p))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation b a m p q)))
def ActualWitnessTransitivity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α)) (a b c m q p r s : OTerm α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation a b m q p))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation b c m r s))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation a c m (add q r) (add s p))))
def ActualWitnessAddition : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α)) (a b c d m q p r s : OTerm α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation a b m q p))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation c d m r s))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation (add a c) (add b d) m (add q r) (add p s))))
def ActualWitnessMultiplication : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α)) (a b m q p c : OTerm α),
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation a b m q p))) →
  Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (equation (mul c a) (mul c b) m (mul c q) (mul c p))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticTargets
