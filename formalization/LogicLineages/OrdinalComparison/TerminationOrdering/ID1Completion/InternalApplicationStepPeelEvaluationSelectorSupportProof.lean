module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSelectorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationStepPeel InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof InternalEqualityTestEvaluationProof

open InternalApplicationStepPeelEvaluationSupportProof

 theorem sourceViewEvaluation (state : Nat) :
    evaluate (source) (List.Vector.ofFn ![state]) = (view state).source := by
  rw [sourceEvaluation]
  rfl

 theorem targetViewEvaluation (state : Nat) :
    evaluate (target) (List.Vector.ofFn ![state]) = (view state).target := by
  rw [targetEvaluation]
  rfl

 theorem stepViewEvaluation (state : Nat) :
    evaluate (step) (List.Vector.ofFn ![state]) = (view state).certificate := by
  rw [stepEvaluation]
  rfl

 theorem rawPathViewEvaluation (state : Nat) :
    evaluate (rawPath) (List.Vector.ofFn ![state]) = (view state).path := by
  rw [rawPathEvaluation,stepViewEvaluation]
  rfl

 theorem pathHeadViewEvaluation (state : Nat) :
    evaluate (pathHead) (List.Vector.ofFn ![state]) = (view state).pathHead := by
  rw [pathHeadEvaluation,rawPathViewEvaluation]
  rfl

 theorem pathTailViewEvaluation (state : Nat) :
    evaluate (pathTail) (List.Vector.ofFn ![state]) = (view state).pathTail := by
  rw [pathTailEvaluation,rawPathViewEvaluation]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSelectorSupportProof
