module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerMapProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryVisitScheduler NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof

theorem tagStepEvaluation (head tail : Nat) :
    evaluate tagStep (head ::ᵥ tail ::ᵥ nil) = 1 + Nat.pair (visitNumber head) tail := by
  rw [tagStep,OriginalHereditaryExpansionEvaluationProof.consEvaluation,
    pairOfEvaluation,constantEvaluation]
  rfl

theorem tagCalibration : OriginalHereditaryVisitSchedulerTargets.TagCalibration := by
  intro jobs
  rw [InternalEqualityTestEvaluationProof.vectorOne]
  simp only [Matrix.cons_val_zero]
  rw [tagVisits,InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation,
    numbersRoundTrip]
  induction jobs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldr_cons,ih,tagStepEvaluation]
    rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerMapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerMapProof
