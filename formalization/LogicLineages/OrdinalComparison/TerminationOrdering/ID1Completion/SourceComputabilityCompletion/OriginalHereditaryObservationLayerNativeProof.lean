module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceRowsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerNativeProof
open OriginalHereditaryObservationLayer OriginalHereditaryObservationLayerTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem native : Native := by
  intro R Q v
  simp only [layer,InternalApplicationCertificateConstructorsEvaluationProof.pairOfEvaluation]

theorem sourcePreservation : SourcePreservation := by
  intro R Q n arity symbols S c hS hR hQ Gamma q r hq hr h
  rw [native,native]
  rw [OriginalHereditaryObservationSourceRootProof.rootPreserves R n arity symbols S c hS hR Gamma q r hq hr h,
    OriginalHereditaryObservationSourceRootProof.rootPreserves Q n arity symbols S c hS hQ Gamma q r hq hr h,
    OriginalHereditaryObservationSourceRowsProof.rowsPreserves Q n arity symbols S c hS hQ Gamma q r hq hr h]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerNativeProof
