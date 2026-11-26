module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionFieldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalPipelineIdentityProof
open UniformCertificateCompletion OriginalLambdaTraversalSelection

/-- Hereditary and step-leaf refinement do not alter the actual selected
Data pipeline. The whole representative and every outer guard are retained. -/
theorem hereditarySelection (q : GlobalSourcePackage.Inputs) :
    OuterSelection.data (OriginalHereditaryLambdaGlobal.finalInputs q).base
      (OriginalHereditaryLambdaGlobal.finalInputs q).window =
      OriginalApplicationSidecar.selectedData q.base q.window := rfl

/-- Literal identity of the final tuple with the unchanged selected sidecar
pipeline applied to the once-prepared original tuple. No earlier leaf Data
is identified with this final Data. -/
theorem finalSelectedData (p : GlobalSourcePackage.Inputs) :
    finalData p = OriginalApplicationSidecar.selectedData
      (preparedData p.base p.window) p.window := hereditarySelection (prepareInputs p)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalPipelineIdentityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalPipelineIdentityProof
