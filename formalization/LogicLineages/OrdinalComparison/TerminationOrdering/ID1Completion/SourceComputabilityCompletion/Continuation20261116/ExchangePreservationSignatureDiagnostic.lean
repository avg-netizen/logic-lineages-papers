module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationCheckerDiagnostic
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationSignatureDiagnostic
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ExchangePreservationDiagnostic (H)
open ExchangePreservationCheckerDiagnostic (signature)
theorem allInputs (v : List.Vector Nat 1) : evaluate H v = signature (v.get 0) := by
  rw [H,InternalAcceptanceCalibrationProof.evalBranch]
  simp only [OriginalRawSyntaxTransportEvaluationSupportProof.constantEvaluation]
  rfl
theorem functionEquality : OriginalTypedDecoder.programValue H = signature := by
  funext x
  exact allInputs (List.Vector.ofFn (fun _ : Fin 1 => x))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationSignatureDiagnostic
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.ExchangePreservationSignatureDiagnostic
