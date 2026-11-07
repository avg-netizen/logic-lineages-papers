module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutExistenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalLinearCombination
open SourceComputabilityFormulaSupportProof
/-- Every positive common divisor is one, entirely in the object language. -/
def coprime {α : Type} (a b : OTerm α) : Formula α :=
  allOne ((arithmeticEmbedding.onFormula (divides (OrdinaryArithmetic.succTerm (.var (.inr 0))) (a.relabel Sum.inl)) ⊓
    arithmeticEmbedding.onFormula (divides (OrdinaryArithmetic.succTerm (.var (.inr 0))) (b.relabel Sum.inl))).imp
    (arithmeticEmbedding.onFormula ((OrdinaryArithmetic.succTerm (.var (.inr 0))).equal
      (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm))))
def ActualPositiveCommonDivisorCombination : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b : OTerm α),
  Nonempty (Derivation body [] (existsOne
    (InternalLeastNumber.minimal (positiveFamily (OrdinaryArithmetic.succTerm a) b) ⊓
      (arithmeticEmbedding.onFormula (divides (OrdinaryArithmetic.succTerm (.var (.inr 0)))
        ((OrdinaryArithmetic.succTerm a).relabel Sum.inl)) ⊓
       arithmeticEmbedding.onFormula (divides (OrdinaryArithmetic.succTerm (.var (.inr 0)))
        (b.relabel Sum.inl))))))
def ActualSignedBezoutFromCoprimality : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b : OTerm α),
  Nonempty (Derivation body [] ((coprime (OrdinaryArithmetic.succTerm a) b).imp
    (arithmeticEmbedding.onFormula (combination (OrdinaryArithmetic.succTerm a) b
      (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutExistenceTargets
