module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryExpansion OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportEvaluationSupportProof OriginalRawSyntaxTransportSelectorProof
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open NumberedMultisetNumeric

theorem consEvaluation {n : Nat} (a b : Program n) (v : List.Vector Nat n) :
    evaluate (consOf a b) v = 1 + Nat.pair (evaluate a v) (evaluate b v) := by
  rw [consOf,binaryCompositionEvaluation,InternalEqualityTestEvaluationProof.vectorTwo]
  exact InternalListCodecEvaluationProof.consEvaluation _ _

theorem childrenEvaluation (raw parameter : Nat) :
    evaluate childJobs (ofFn ![raw,parameter]) = numbersNumber (childValues raw parameter) := by
  simp only [childJobs,firstJob,secondJob,firstParameter,evalBranch,sameOfEvaluation,
    arityOfEvaluation,firstOfEvaluation,secondOfEvaluation,pairOfEvaluation,
    consEvaluation,leftOfEvaluation,rightOfEvaluation,constantEvaluation,
    evaluate,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold childValues tagValue
  split_ifs <;> simp_all [numbersNumber]

theorem deletionsEvaluation (raw parameter : Nat) :
    evaluate deletionJobs (ofFn ![raw,parameter]) = numbersNumber (deletionValues raw parameter) := by
  rw [deletionJobs,binaryCompositionEvaluation,pairOfEvaluation,constantEvaluation]
  change evaluate (OriginalHereditaryDeletionRows.rows unpackJob)
    (ofFn ![Nat.pair 0 raw,parameter]) = _
  exact OriginalHereditaryDeletionRowsBoundProof.nativeRows unpackJob _ _

theorem totalCalibration : OriginalHereditaryExpansionTargets.TotalCalibration := by
  intro raw parameter
  rw [expansion,binaryCompositionEvaluation,childrenEvaluation,deletionsEvaluation]
  exact OriginalContextInsertionCalibrationProof.appendNumbers _ _

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionEvaluationProof
