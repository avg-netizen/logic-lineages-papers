module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalBinaryCRT
/-- Genuine internal binary CRT: coprimality, not a supplied certificate, is the only premise. -/
def ActualBinaryCRT : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (a b r s : OTerm α),
  Nonempty (Derivation body [] ((InternalBezoutExistenceTargets.coprime
    (OrdinaryArithmetic.succTerm a) (OrdinaryArithmetic.succTerm b)).imp
    (solution (OrdinaryArithmetic.succTerm a) (OrdinaryArithmetic.succTerm b) r s)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTTargets
