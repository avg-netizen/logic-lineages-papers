module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeInputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityInputProof
open OriginalFunctionNeutrality UniformCertificateCompletion

/-- The neutral-observer guard changes only the original representative
field. All original raw-input calibrations of the supplied tuple remain. -/
theorem refinedInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (refineInputs p) := by
  obtain ⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩ := hp
  have hnewbase := (OriginalFunctionNeutralityEvaluationProof.actualOriginalFunctionNeutralityRefinementEquality
    n arity p.base p.window hbase hwindow).2
  exact ⟨hnewbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩

/-- Reuse the complete existing shape/neutral/variable pipeline after the
new all-input-equal representative guard, on the same original input tuple. -/
theorem finalInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (finalInputs p) :=
  OriginalConstructorShapeInputProof.finalInputsCalibrated n arity (refineInputs p)
    (refinedInputsCalibrated n arity p hp)

theorem finalWindow (p : GlobalSourcePackage.Inputs) : (finalInputs p).window = p.window := by
  change (OriginalConstructorShape.finalInputs (refineInputs p)).window = p.window
  rw [OriginalConstructorShapeInputProof.finalWindow]
  rfl

/-- Identify the exact Data used by the final source with the Data of the
new internal neutrality theorem. No independently selected package is used. -/
theorem finalSelectedData (p : GlobalSourcePackage.Inputs) :
    OuterSelection.data (finalInputs p).base (finalInputs p).window =
      selectedData p.base p.window := by
  change OuterSelection.data (OriginalConstructorShape.finalInputs (refineInputs p)).base
      (OriginalConstructorShape.finalInputs (refineInputs p)).window = _
  rw [OriginalConstructorShapeInputProof.finalSelectedData]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityInputProof
