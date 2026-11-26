module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
open UniformCertificateCompletion

/-- Apply the accepted constructor and representative refinements to the
supplied original tuple, retaining that tuple instead of selecting a new one. -/
theorem variableInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (OriginalVariableRepresentative.refineInputs p) := by
  obtain ⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩ := hp
  obtain ⟨_,hnewbase⟩ :=
    OriginalVariableRepresentativeEvaluationProof.actualOriginalVariableRepresentativeRefinementEquality
      n arity p.base p.window hbase hwindow
  have hstepEq := OriginalConstructorLeafEvaluationProof.actualOriginalConstructorLeafRefinementEquality
    n arity p.oldStep hstep
  refine ⟨hnewbase,hwindow,hsrc,hcomp,?_,hvertex,hresult⟩
  intro v
  exact (hstepEq v).trans (hstep v)


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
