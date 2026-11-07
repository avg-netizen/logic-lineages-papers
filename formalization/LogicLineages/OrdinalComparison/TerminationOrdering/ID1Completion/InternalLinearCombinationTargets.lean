module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalLinearCombination SourceComputabilityFormulaSupportProof
abbrev ef {α : Type} (p : OrdinaryArithmetic.Formula α) : Formula α := arithmeticEmbedding.onFormula p
def ActualRemainderClosure : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b d q r : OTerm α),
  Nonempty (Derivation body [] ((ef (combination a b d) ⊓
    ef (a.equal (OrdinaryArithmetic.addTerm (OrdinaryArithmetic.mulTerm q d) r)) ).imp
      (ef (combination a b r))))
def ActualSymmetry : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b d : OTerm α),
  Nonempty (Derivation body [] ((ef (combination a b d)).imp (ef (combination b a d))))
def ActualPositiveMinimum : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b : OTerm α),
  Nonempty (Derivation body [] (existsOne
    (InternalLeastNumber.minimal (positiveFamily (OrdinaryArithmetic.succTerm a) b))))
def ActualMinimumDivides : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b e : OTerm α),
  Nonempty (Derivation body [] ((instantiate (InternalLeastNumber.minimal (positiveFamily a b))
    (arithmeticEmbedding.onTerm e)).imp
    (ef (divides (OrdinaryArithmetic.succTerm e) a) ⊓ ef (divides (OrdinaryArithmetic.succTerm e) b))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationTargets
