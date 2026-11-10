module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFullFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeRootFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableEndpointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalFieldsProof
open OriginalFunctionNeutrality OriginalFunctionNeutralityInputProof UniformCertificateCompletion

/-- Prior constructor fields hold for the exact final tuple's data. -/
theorem finalRootFields (p : GlobalSourcePackage.Inputs) :
    OriginalConstructorShape.FullFoldRootFields
      (OuterSelection.data (finalInputs p).base (finalInputs p).window)
      (finalInputs p).window := by
  rw [finalSelectedData,finalWindow]
  exact OriginalConstructorShapeRootFieldsProof.fullFoldRootFields
    (baseData p.base p.window) p.window

/-- Neutrality reflection uses the same selected data and window. -/
theorem finalMarkPreservation (p : GlobalSourcePackage.Inputs) :
    FullFoldMarkPreservation
      (OuterSelection.data (finalInputs p).base (finalInputs p).window)
      (finalInputs p).window := by
  rw [finalSelectedData,finalWindow]
  exact OriginalFunctionNeutralityFullFoldProof.fullFoldMarkPreservation p.base p.window

/-- The original neutral law remains at the final tuple's own endpoint
and once-refined step leaf, after both representative guards. -/
theorem finalNeutralBottom (p : GlobalSourcePackage.Inputs) :
    OriginalNeutralLeaf.NeutralBottom (OriginalNeutralLeaf.endpoint (finalInputs p))
      (finalInputs p).window (finalInputs p).oldStep :=
  OriginalNeutralVariableProof.finalNeutralLaw
    (OriginalConstructorShape.refineInputs (refineInputs p))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalFieldsProof
