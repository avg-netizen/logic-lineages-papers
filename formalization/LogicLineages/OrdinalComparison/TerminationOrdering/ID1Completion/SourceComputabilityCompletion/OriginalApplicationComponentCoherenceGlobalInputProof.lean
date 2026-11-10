module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalInputProof
open OriginalApplicationSidecar UniformCertificateCompletion

/-- All-input equality changes only the original representative field.
The source, computability, step, vertex, result and window suppliers remain. -/
theorem refinedInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (refineInputs p) := by
  obtain ⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩ := hp
  have hnewbase := (OriginalApplicationSidecarCalibrationProof.actualOriginalApplicationSidecarRefinementEquality
    n arity p.base p.window hbase hwindow).2
  exact ⟨hnewbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩

/-- Apply the unchanged once-only final pipeline to the calibrated refinement. -/
theorem finalInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (finalInputs p) :=
  OriginalFunctionNeutralityInputProof.finalInputsCalibrated n arity (refineInputs p)
    (refinedInputsCalibrated n arity p hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalInputProof
