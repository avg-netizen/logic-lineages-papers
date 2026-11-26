module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialSource.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialCalibration.Targets
open UniformCertificateCompletion
/-- Native calibration of the explicit NEW tuple and its literal installed tuple only. -/
def NativeAlignedCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  GlobalSourcePackage.InputsCalibrated n arity (OriginalAlignedInitialSource.alignedInputs n p) ∧
  GlobalSourcePackage.InputsCalibrated n arity (OriginalAlignedInitialSource.installedInputs n arity p)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalAlignedInitialCalibration.Targets
