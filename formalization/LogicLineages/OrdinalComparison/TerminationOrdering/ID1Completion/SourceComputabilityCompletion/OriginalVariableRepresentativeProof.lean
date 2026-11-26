module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeRigidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeProof
open OriginalVariableRepresentative UniformCertificateCompletion

/-- Select the original Inputs once, retain its paid once-refined oldStep,
and guard only base.oldRepresentative before ANY window or Gamma. -/
theorem actualOriginalVariableRepresentativeGlobalSelection :
    OriginalVariableRepresentativeTargets.ActualOriginalVariableRepresentativeGlobalSelection := by
  intro n arity
  obtain ⟨p,hp,he,hq,hpackage,hfactor,hcases⟩ :=
    OriginalConstructorLeafProof.actualOriginalConstructorLeafGlobalSelection n arity
  let q := OriginalConstructorLeaf.refineInputs p
  obtain ⟨hr,hbase⟩ := OriginalVariableRepresentativeEvaluationProof.actualOriginalVariableRepresentativeRefinementEquality
    n arity q.base q.window hq.1 hq.2.1
  have hfinal : GlobalSourcePackage.InputsCalibrated n arity (refineInputs p) :=
    ⟨hbase,hq.2⟩
  refine ⟨p,hp,he,hr,hfinal,?_,hfactor,hcases,?_,?_⟩
  · exact (GlobalSourcePackageProof.actualOriginalGlobalSourcePackageConstruction
      n arity (refineInputs p) hfinal).2.2
  · exact OriginalVariableRepresentativeSelectedProof.selectedMarkPreservation p.base p.window
  · exact OriginalVariableRepresentativeRigidityProof.fullFoldRigidity p.base p.window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeProof
