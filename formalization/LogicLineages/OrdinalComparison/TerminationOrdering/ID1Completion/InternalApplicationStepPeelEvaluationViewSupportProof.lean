module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationFieldSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationViewSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationStepPeel InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof InternalEqualityTestEvaluationProof

open InternalApplicationStepPeelEvaluationSupportProof

open InternalApplicationStepPeelEvaluationSelectorSupportProof

open InternalApplicationStepPeelEvaluationFieldSupportProof

 theorem functionCodeViewEvaluation (state : Nat) :
    evaluate functionCode (List.Vector.ofFn ![state]) = (endpointInputs (view state)).get 2 := by
  rw [functionCodeEvaluation,arrowTypeEvaluation,domainViewEvaluation,codomainViewEvaluation,functionPayload_sourceViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

 theorem targetFunctionCodeViewEvaluation (state : Nat) :
    evaluate targetFunctionCode (List.Vector.ofFn ![state]) = (endpointInputs (view state)).get 3 := by
  rw [targetFunctionCodeEvaluation,arrowTypeEvaluation,domainViewEvaluation,codomainViewEvaluation,functionPayload_targetViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

 theorem argumentCodeViewEvaluation (state : Nat) :
    evaluate argumentCode (List.Vector.ofFn ![state]) = (endpointInputs (view state)).get 4 := by
  rw [argumentCodeEvaluation,domainViewEvaluation,argumentPayload_sourceViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

 theorem peeledStepViewEvaluation (state : Nat) :
    evaluate peeledStep (List.Vector.ofFn ![state]) =
      Nat.pair (view state).pathTail (view state).payload := by
  rw [peeledStepEvaluation,pathTailViewEvaluation,stepViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationViewSupportProof
