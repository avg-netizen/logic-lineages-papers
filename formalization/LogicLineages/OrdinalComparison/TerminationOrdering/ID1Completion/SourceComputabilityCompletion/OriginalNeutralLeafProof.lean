module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafProof
open OriginalNeutralLeaf UniformCertificateCompletion

/-- Every original global input contract survives the one literal oldStep
refinement. All other input ASTs are unchanged. -/
theorem refinedInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (refineInputs p) := by
  obtain ⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩ := hp
  refine ⟨hbase,hwindow,hsrc,hcomp,?_,hvertex,hresult⟩
  intro v
  exact (OriginalNeutralLeafEvaluationProof.actualOriginalNeutralLeafRefinementEquality
    n arity p ⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩ v).trans (hstep v)

/-- Native redundancy and internal zero-guard inversion are separately paid
for one global tuple before the original all-window package is obtained. -/
theorem actualOriginalNeutralLeafGlobalSelection :
    OriginalNeutralLeafTargets.ActualOriginalNeutralLeafGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  have hq := refinedInputsCalibrated n arity p hp
  refine ⟨p,hp,?_,hq,?_,?_,?_⟩
  · exact OriginalNeutralLeafEvaluationProof.actualOriginalNeutralLeafRefinementEquality n arity p hp
  · exact (GlobalSourcePackageProof.actualOriginalGlobalSourcePackageConstruction
      n arity (refineInputs p) hq).2.2
  · exact OriginalNeutralLeafInternalProof.originalFactor (endpoint p) p.window p.oldStep
  · exact OriginalNeutralLeafInternalProof.neutralLaw (endpoint p) p.window p.oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafProof
