module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceTargets
open UniformCertificateCompletion
open OriginalFinalObjectCoherence

/-- No extra native calibration, final-fold equation, output witness or
representative transport premise is supplied by the caller. -/
def ActualOriginalFinalObjectCanonicalCancellation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p → Cancellation n arity p

def ActualOriginalFinalObjectRankInvariance : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p → RankInvariance n arity p

/-- One original calibrated input tuple before all finite windows and
runtime contexts, retaining the entire accepted global selection package. -/
def ActualOriginalFinalObjectGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧ Properties n arity p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceTargets
