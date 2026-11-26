module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalPackageProof
open OriginalFunctionNeutrality UniformCertificateCompletion

/-- The complete original package at the exact final refined tuple. The
calibration supplier remains separate from the internal fold arguments. -/
theorem finalPackage (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.Package n arity
      (GlobalSourcePackage.source (finalInputs p))
      (GlobalSourcePackage.computability (finalInputs p))
      (GlobalSourcePackage.lift (finalInputs p)) := by
  have hr := OriginalFunctionNeutralityInputProof.finalInputsCalibrated n arity p hp
  exact (GlobalSourcePackageProof.actualOriginalGlobalSourcePackageConstruction
    n arity (finalInputs p) hr).2.2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalPackageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalPackageProof
