module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalSquareRootArithmetic
abbrev suc {α : Type} := @OrdinaryArithmetic.succTerm α
abbrev ltF {α : Type} (s t : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t)
abbrev eqF {α : Type} (s t : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (s.equal t)
def ActualSuccessorSquareExpansion : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (eqF (square (suc s))
    (OrdinaryArithmetic.addTerm (square s) (suc (OrdinaryArithmetic.addTerm s s)))))
def ActualSuccessorSquareStrict : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (ltF (square s) (square (suc s))))
def ActualSquareStrictMonotonicity : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((ltF s t).imp (ltF (square s) (square t))))
def ActualSquareIntervalZero : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type),
  Nonempty (Derivation body [] (interval (OrdinaryArithmetic.zeroTerm : OrdinaryArithmetic.Term α)
    OrdinaryArithmetic.zeroTerm))
def ActualSquareIntervalUniqueness : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s t n : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((interval s n ⊓ interval t n).imp (eqF s t)))
def ActualSquareBoundaryCrossing : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s n : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((interval s n ⊓ (ltF (suc n) (square (suc s))).not).imp
    (eqF (suc n) (square (suc s)))))
def ActualSquareIntervalRetain : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s n : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((interval s n ⊓ ltF (suc n) (square (suc s))).imp
    (interval s (suc n))))
def ActualSquareIntervalAdvance : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (s n : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((interval s n ⊓ (ltF (suc n) (square (suc s))).not).imp
    (interval (suc s) (suc n))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticTargets
