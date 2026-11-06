module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticTargets
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open InternalCalculus

/-- Actual derivations for the ORIGINAL multiplication-based tag, not merely
standard-N identities and not an alternative coding definition. -/
def ActualEvenTagZero : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((tagTerm false (OrdinaryArithmetic.zeroTerm : OrdinaryArithmetic.Term α)).equal
      OrdinaryArithmetic.zeroTerm)))

def ActualEvenTagSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    ((tagTerm false (OrdinaryArithmetic.succTerm t)).equal
      (OrdinaryArithmetic.succTerm (OrdinaryArithmetic.succTerm (tagTerm false t))))))

/-- Internal cancellation for either ORIGINAL numerical tag. -/
def ActualTagInjectivity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (odd : Bool) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    (((tagTerm odd s).equal (tagTerm odd t)).imp (s.equal t))))

/-- Internal disjointness, with no semantic premise or extra arithmetic rule. -/
def ActualTagsDisjoint : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (arithmeticEmbedding.onFormula
    (((tagTerm false s).equal (tagTerm true t)).not)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticTargets
