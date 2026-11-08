module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSelectorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationFieldSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationStepPeel InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof InternalEqualityTestEvaluationProof

open InternalApplicationStepPeelEvaluationSupportProof

open InternalApplicationStepPeelEvaluationSelectorSupportProof

 theorem outerType_sourceViewEvaluation (state : Nat) :
    evaluate (outerType source) (List.Vector.ofFn ![state]) = (view state).sourceType := by
  rw [outerTypeEvaluation,sourceViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem outerType_targetViewEvaluation (state : Nat) :
    evaluate (outerType target) (List.Vector.ofFn ![state]) = (view state).targetType := by
  rw [outerTypeEvaluation,targetViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem constructorTag_sourceViewEvaluation (state : Nat) :
    evaluate (constructorTag source) (List.Vector.ofFn ![state]) = (view state).sourceTag := by
  rw [constructorTagEvaluation,sourceViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem constructorTag_targetViewEvaluation (state : Nat) :
    evaluate (constructorTag target) (List.Vector.ofFn ![state]) = (view state).targetTag := by
  rw [constructorTagEvaluation,targetViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem appDomain_sourceViewEvaluation (state : Nat) :
    evaluate (appDomain source) (List.Vector.ofFn ![state]) = (view state).domain := by
  rw [appDomainEvaluation,appBodyEvaluation,sourceViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem appDomain_targetViewEvaluation (state : Nat) :
    evaluate (appDomain target) (List.Vector.ofFn ![state]) = (view state).targetDomain := by
  rw [appDomainEvaluation,appBodyEvaluation,targetViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem functionPayload_sourceViewEvaluation (state : Nat) :
    evaluate (functionPayload source) (List.Vector.ofFn ![state]) = (view state).functionPayload := by
  rw [functionPayloadEvaluation,appBodyEvaluation,sourceViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem functionPayload_targetViewEvaluation (state : Nat) :
    evaluate (functionPayload target) (List.Vector.ofFn ![state]) = (view state).targetFunctionPayload := by
  rw [functionPayloadEvaluation,appBodyEvaluation,targetViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem argumentPayload_sourceViewEvaluation (state : Nat) :
    evaluate (argumentPayload source) (List.Vector.ofFn ![state]) = (view state).argumentPayload := by
  rw [argumentPayloadEvaluation,appBodyEvaluation,sourceViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem argumentPayload_targetViewEvaluation (state : Nat) :
    evaluate (argumentPayload target) (List.Vector.ofFn ![state]) = (view state).targetArgumentPayload := by
  rw [argumentPayloadEvaluation,appBodyEvaluation,targetViewEvaluation]
  simp only [view,endpointInputs,List.Vector.get_ofFn]

 theorem domainViewEvaluation (state : Nat) :
    evaluate domain (List.Vector.ofFn ![state]) = (view state).domain := by
  rw [domainEvaluation,appDomain_sourceViewEvaluation]

 theorem codomainViewEvaluation (state : Nat) :
    evaluate codomain (List.Vector.ofFn ![state]) = (view state).sourceType := by
  rw [codomainEvaluation,outerType_sourceViewEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationFieldSupportProof
