module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportLeafRebuildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportConstructorEvaluationProof
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransportEvaluationSupportProof OriginalRawSyntaxTransportLeafRebuildProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem variableConstructorEvaluation (v : List.Vector Nat 1) :
    evaluate variableConstructor v = Nat.pair 0 (v.get 0) := by
  simp only [variableConstructor, pairOfEvaluation, constantEvaluation, projectionEvaluation]

 theorem lambdaConstructorEvaluation (v : List.Vector Nat 2) :
    evaluate lambdaConstructor v = Nat.pair 1 (Nat.pair (v.get 0) (v.get 1)) := by
  simp only [lambdaConstructor, pairOfEvaluation, constantEvaluation, projectionEvaluation]

 theorem applicationConstructorEvaluation (v : List.Vector Nat 3) :
    evaluate applicationConstructor v = Nat.pair 2 (Nat.pair (v.get 0) (Nat.pair (v.get 1) (v.get 2))) := by
  simp only [applicationConstructor, pairOfEvaluation, constantEvaluation, projectionEvaluation]

 theorem bottomConstructorEvaluation (v : List.Vector Nat 1) :
    evaluate bottomConstructor v = Nat.pair 3 (v.get 0) := by
  simp only [bottomConstructor, pairOfEvaluation, constantEvaluation, projectionEvaluation]

 theorem ordinaryConstructorEvaluation (v : List.Vector Nat 2) :
    evaluate ordinaryConstructor v = Nat.pair 4 (Nat.pair (v.get 0) (v.get 1)) := by
  simp only [ordinaryConstructor, pairOfEvaluation, constantEvaluation, projectionEvaluation]

 theorem numberedConstructorEvaluation (v : List.Vector Nat 6) :
    evaluate numberedConstructor v = Nat.pair 5 (Nat.pair (v.get 0) (Nat.pair (v.get 1)
      (Nat.pair (v.get 2) (Nat.pair (v.get 3) (Nat.pair (v.get 4) (v.get 5)))))) := by
  simp only [numberedConstructor, pairOfEvaluation, constantEvaluation, projectionEvaluation]

 theorem nilConstructorEvaluation (v : List.Vector Nat 0) :
    evaluate nilConstructor v = Nat.pair 6 0 := by
  simp only [nilConstructor, pairOfEvaluation, constantEvaluation]

 theorem consConstructorEvaluation (v : List.Vector Nat 3) :
    evaluate consConstructor v = Nat.pair 7 (Nat.pair (v.get 0) (Nat.pair (v.get 1) (v.get 2))) := by
  simp only [consConstructor, pairOfEvaluation, constantEvaluation, projectionEvaluation]

 theorem variableActionEvaluation (mode : Mode) (v : List.Vector Nat 3) :
    evaluate (variableAction mode) v = leafValue mode (v.get 0) (v.get 1) (Nat.pair 0 (v.get 2)) := by
  rw [variableAction, ternaryCompositionEvaluation, leafEvaluation]
  change leafValue mode (v.get 0) (v.get 1)
    (evaluate variableConstructor (List.Vector.ofFn ![v.get 2])) = _
  rw [variableConstructorEvaluation]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportConstructorEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportConstructorEvaluationProof
