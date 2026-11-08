module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationViewSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalApplicationStepPeel InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof InternalEqualityTestEvaluationProof

open InternalApplicationStepPeelEvaluationSupportProof

open InternalApplicationStepPeelEvaluationViewSupportProof
open InternalApplicationStepPeelEvaluationSelectorSupportProof InternalApplicationStepPeelEvaluationFieldSupportProof

 theorem endpointVectorEvaluation (state : Nat) :
    (List.Vector.ofFn fun i : Fin 5 => evaluate
      ((![domain,codomain,functionCode,targetFunctionCode,argumentCode] : Fin 5 → Program 1) i)
      (List.Vector.ofFn ![state])) = endpointInputs (view state) := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))) i <;>
    simp only [List.Vector.get_ofFn]
  · exact domainViewEvaluation state
  · exact codomainViewEvaluation state
  · exact functionCodeViewEvaluation state
  · exact targetFunctionCodeViewEvaluation state
  · exact argumentCodeViewEvaluation state




 theorem endpointTypeGuardEvaluation (v : View) :
    evaluate endpointTypeGuard (endpointInputs v) = 1 := by
  simp [endpointTypeGuard,conjunctionEvaluation,sameEvaluation,
    leftOfEvaluation,consOfEvaluation,projectionEvaluation,endpointInputs,Nat.unpair_pair]


 theorem endpointAtEvaluation (endpoint : Program 5) (state : Nat) :
    evaluate (endpointAt endpoint) (List.Vector.ofFn ![state]) =
      if evaluate endpoint (endpointInputs (view state)) = 1 then 1 else 0 := by
  change evaluate (endpointGuard endpoint)
    (List.Vector.ofFn fun i : Fin 5 => evaluate
      ((![domain,codomain,functionCode,targetFunctionCode,argumentCode] : Fin 5 → Program 1) i)
      (List.Vector.ofFn ![state])) = _
  rw [endpointVectorEvaluation,endpointGuard,conjunctionEvaluation,endpointTypeGuardEvaluation]
  simp


 theorem structuralGuardEvaluation (state : Nat) :
    evaluate structuralGuard (List.Vector.ofFn ![state]) =
      if shape (view state) then 1 else 0 := by
  unfold structuralGuard
  simp only [conjunctionEvaluation,sameEvaluation,nonemptyPathEvaluation,twoEvaluation,
    rawPathViewEvaluation,pathHeadViewEvaluation,constructorTag_sourceViewEvaluation,
    constructorTag_targetViewEvaluation,outerType_sourceViewEvaluation,outerType_targetViewEvaluation,
    appDomain_sourceViewEvaluation,appDomain_targetViewEvaluation,
    argumentPayload_sourceViewEvaluation,argumentPayload_targetViewEvaluation]
  simp only [shape, ite_eq_left_iff, ite_eq_right_iff]
  simp




 theorem peeledStateEvaluation (state : Nat) :
    evaluate peeledState (List.Vector.ofFn ![state]) = peeledValue state := by
  change evaluate edgeCode (List.Vector.ofFn fun i : Fin 3 =>
    evaluate ((![functionCode,targetFunctionCode,peeledStep] : Fin 3 → Program 1) i)
      (List.Vector.ofFn ![state])) = _
  rw [edgeCodeEvaluation]
  change Nat.pair (evaluate functionCode (List.Vector.ofFn ![state]))
    (Nat.pair (evaluate targetFunctionCode (List.Vector.ofFn ![state]))
      (evaluate peeledStep (List.Vector.ofFn ![state]))) = _
  rw [functionCodeViewEvaluation,targetFunctionCodeViewEvaluation,peeledStepViewEvaluation]
  rfl




 theorem actualOriginalTransitionCalibration :
    InternalApplicationStepPeelTargets.ActualOriginalTransitionCalibration := by
  intro n arity symbols S Gamma endpoint calibrated state
  have hg : evaluate (guard endpoint) (List.Vector.ofFn ![state]) =
      guardValue n arity symbols S Gamma state := by
    rw [InternalApplicationStepPeel.guard,conjunctionEvaluation,structuralGuardEvaluation,endpointAtEvaluation,calibrated]
    simp [guardValue]
  refine ⟨hg, ?_⟩
  rw [transition,evalBranch,hg,peeledStateEvaluation,projectionEvaluation,List.Vector.get_ofFn]
  unfold transitionValue guardValue
  split <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationProof
