module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafEquationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalCanonicalFoldFusion
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The sidecar and C have the SAME literal raw application combiner.
Only their child graphs are compared; no type, validity or native theorem
about C's outputs is supplied to this application step. -/
theorem sidecarApplicationLaw (data rawData : Data) (window : Program 1) :
    ApplicationLaw (OriginalApplicationSidecar.originalData data window) window
      (OriginalApplicationSidecar.fold data window)
      (OriginalLambdaTraversalSelection.canonical rawData window) := by
  intro body alpha Delta arrow d e fp ap fn arg input functionOut argumentOut out typ parameter
    hc hp hf ha hcf hca
  have hr := OriginalApplicationSidecarEquationSupportProof.applicationBackward data window
    arrow d e fp ap fn arg input functionOut argumentOut out parameter hc
    (andLeft (andLeft (andRight hp))) hf ha (andRight (andRight hp))
  exact OriginalLambdaTraversalInternalApplicationProof.applicationBackward
    (OriginalLambdaTraversalSelection.leaf rawData window)
    input d e fn arg parameter functionOut argumentOut out
    (OriginalLambdaTraversalApplicationFieldsProof.fromConstructors arrow d e fp ap fn arg input hc)
    hcf hca hr

/-- The ACTUAL final full fold's existing internal application equation
already pays its own combine leaf. It is compared with C's unconditional
internal recurrence at the same literal original application fields. -/
theorem canonicalApplicationLaw (data rawData : Data) (window : Program 1) :
    ApplicationLaw (OriginalApplicationSidecar.selectedData data window) window
      (InternalParameterizedCanonicalResultFold.foldN (OriginalApplicationSidecar.selectedData data window))
      (OriginalLambdaTraversalSelection.canonical rawData window) := by
  intro body alpha Delta arrow d e fp ap fn arg input functionOut argumentOut out typ parameter
    hc hp hf ha hcf hca
  have hr := OriginalApplicationSidecarSameLeafEquationProof.canonicalRecover data window
    arrow d e fp ap fn arg input functionOut argumentOut out parameter
    (andLeft hp) hc (andLeft (andLeft (andRight hp))) hf ha (andRight (andRight hp))
  exact OriginalLambdaTraversalInternalApplicationProof.applicationBackward
    (OriginalLambdaTraversalSelection.leaf rawData window)
    input d e fn arg parameter functionOut argumentOut out
    (OriginalLambdaTraversalApplicationFieldsProof.fromConstructors arrow d e fp ap fn arg input hc)
    hcf hca hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionApplicationProof
