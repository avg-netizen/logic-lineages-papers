module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafProof
open OriginalConstructorLeaf UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Select before all windows; alter only the oldStep AST. Calibration,
internal cases and the original unqualified R005 package are separately paid. -/
theorem actualOriginalConstructorLeafGlobalSelection :
    OriginalConstructorLeafTargets.ActualOriginalConstructorLeafGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  obtain ⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩ := hp
  have he := OriginalConstructorLeafEvaluationProof.actualOriginalConstructorLeafRefinementEquality
    n arity p.oldStep hstep
  have hq : GlobalSourcePackage.InputsCalibrated n arity (refineInputs p) := by
    refine ⟨hbase,hwindow,hsrc,hcomp,?_,hvertex,hresult⟩
    intro v
    exact (he v).trans (hstep v)
  refine ⟨p,⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩,he,hq,?_,?_,?_⟩
  · exact (GlobalSourcePackageProof.actualOriginalGlobalSourcePackageConstruction
      n arity (refineInputs p) hq).2.2
  · exact OriginalConstructorLeafInternalProof.originalFactor p.oldStep
  · exact OriginalConstructorLeafInternalProof.constructorCases p.oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafProof
