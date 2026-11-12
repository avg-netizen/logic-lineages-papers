module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeGeometryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentApplicationFunctionDefinitions OriginalTransparentApplicationFunctionEvaluationProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationProof

def state (v : List.Vector Nat 4) : Nat := Nat.pair (v.get 0) (Nat.pair (v.get 1) (v.get 2))

theorem edgeEvaluation (v : List.Vector Nat 4) : evaluate edge v = state v := by
 change evaluate InternalApplicationCertificateConstructors.edgeCode (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2]) = _
 rw [edgeCodeEvaluation]
 rfl

theorem atEdgeEvaluation (P : Program 1) (v : List.Vector Nat 4) :
 evaluate (atEdge P) v = evaluate P (List.Vector.ofFn ![state v]) := by
 change evaluate P (List.Vector.ofFn (fun _ : Fin 1 => evaluate edge v)) = _
 rw [edgeEvaluation]
 apply congrArg (evaluate P)
 apply congrArg List.Vector.ofFn
 funext i
 have hi : i = 0 := Fin.eq_zero i
 subst i
 rfl

theorem shapeOfGuard (v : List.Vector Nat 4) (h : evaluate structuralGuard v = 1) :
 InternalApplicationStepPeel.shape (InternalApplicationStepPeel.view (state v)) = true := by
 rw [structuralGuard,atEdgeEvaluation,structuralGuardEvaluation] at h
 split at h
 next ht => exact ht
 next => contradiction

theorem sourceTag (v : List.Vector Nat 4) (h : evaluate structuralGuard v = 1) :
 (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 2 := by
 have hs := (of_decide_eq_true (shapeOfGuard v h)).2.2.1
 simpa only [InternalApplicationStepPeel.view,state,Nat.unpair_pair] using hs

theorem childrenAtState (v : List.Vector Nat 4) :
 (childValues v).get 0 = (InternalApplicationStepPeel.endpointInputs (InternalApplicationStepPeel.view (state v))).get 2 ∧
 (childValues v).get 1 = (InternalApplicationStepPeel.endpointInputs (InternalApplicationStepPeel.view (state v))).get 3 ∧
 (childValues v).get 2 = Nat.pair (InternalApplicationStepPeel.view (state v)).pathTail
   (InternalApplicationStepPeel.view (state v)).payload ∧
 (childValues v).get 3 = v.get 3 := by
 simp only [childValues,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
 Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
 sourceFunction,targetFunction,childCertificate,atEdgeEvaluation]
 simp [InternalApplicationStepPeelEvaluationSupportProof.functionCodeEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.targetFunctionCodeEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.peeledStepEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.arrowTypeEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.domainEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.codomainEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.appDomainEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.appBodyEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.outerTypeEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.functionPayloadEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.sourceEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.targetEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.rawPathEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.pathTailEvaluation,
 InternalApplicationStepPeelEvaluationSupportProof.stepEvaluation,
 rightOfEvaluation,InternalApplicationStepPeel.endpointInputs,InternalApplicationStepPeel.view]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeGeometryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeGeometryProof
