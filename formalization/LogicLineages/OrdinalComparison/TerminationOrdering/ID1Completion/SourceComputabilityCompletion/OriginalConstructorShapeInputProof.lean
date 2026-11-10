module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeInputProof
open OriginalConstructorShape UniformCertificateCompletion

/-- Only the supplied tuple's representative is guarded. Every other input
contract is retained literally, before any source window is selected. -/
theorem refinedInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (refineInputs p) := by
  obtain ⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩ := hp
  have hnewbase := (OriginalConstructorShapeEvaluationProof.actualOriginalConstructorShapeRefinementEquality
    n arity p.base p.window hbase hwindow).2
  exact ⟨hnewbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩

/-- The frozen shape, neutral-leaf and variable refinements apply in this
order to the same supplied tuple; none of them selects new global inputs. -/
theorem finalInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (finalInputs p) := by
  have hshape := refinedInputsCalibrated n arity p hp
  have hneutral := OriginalNeutralLeafProof.refinedInputsCalibrated n arity (refineInputs p) hshape
  exact OriginalNeutralVariableProof.variableInputsCalibrated n arity
    (OriginalNeutralLeaf.refineInputs (refineInputs p)) hneutral

theorem finalWindow (p : GlobalSourcePackage.Inputs) : (finalInputs p).window = p.window := by
  simp only [finalInputs,OriginalVariableRepresentative.refineInputs,
    OriginalConstructorLeaf.refineInputs,OriginalNeutralLeaf.refineInputs,refineInputs]

/-- Record-field reduction identifies the final source's selected Data with
the exact Data in the independently frozen full-fold shape contract. The
actual program definitions remain folded during this comparison. -/
theorem finalSelectedData (p : GlobalSourcePackage.Inputs) :
    OuterSelection.data (finalInputs p).base (finalInputs p).window =
      selectedData p.base p.window := by
  simp only [finalInputs,OriginalVariableRepresentative.refineInputs,
    OriginalConstructorLeaf.refineInputs,OriginalNeutralLeaf.refineInputs,refineInputs,
    selectedData,OriginalVariableRepresentative.selectedData]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeInputProof
