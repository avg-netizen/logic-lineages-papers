module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeEvaluationProof
open Source InternalOriginalUniformParameterLeaves
open OriginalClassContextAllPositionObserver OriginalClassContextAllPositionNativeSelectorsProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open OriginalActiveClassKernelEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem observationEvaluation (R : Program 2) (v : List.Vector Nat 3) :
    evaluate (positionObservation R) v =
      Nat.pair (evaluate R (ofFn ![evaluate erasedPacked v,evaluate erasedParameter v]))
        (evaluate OriginalRawSyntaxTransport.variableRankPackedRaw (ofFn ![evaluate erasedPacked v])) := by
  rw [positionObservation,pairOfEvaluation]
  rfl

theorem observationSlice (R : Program 2) (context value : Nat) (binders Gamma : List Ty) (sigma : Ty) :
    evaluate (positionObservation R)
      (ofFn ![binders.length,value,Nat.pair context (Encodable.encode (binders ++ sigma :: Gamma))]) =
    Nat.pair (evaluate R (ofFn ![OriginalClassContextPrefixNative.erasedPacked binders sigma value,
      Nat.pair context (Encodable.encode (binders ++ Gamma))]))
      (evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
        (ofFn ![OriginalClassContextPrefixNative.erasedPacked binders sigma value])) := by
  rw [observationEvaluation,erasedPackedSlice,erasedParameterSlice]

theorem testEvaluation (R : Program 2) (v : List.Vector Nat 4) :
    evaluate (positionTest R) v =
      if evaluate (positionObservation R) (ofFn ![v.get 0,v.get 1,v.get 3]) =
        evaluate (positionObservation R) (ofFn ![v.get 0,v.get 2,v.get 3]) then 1 else 0 := by
  rw [positionTest,sameEvaluation]
  rfl

theorem scanZero (R : Program 2) (seed candidate parameter : Nat) :
    evaluate (scan R) (ofFn ![0,seed,candidate,parameter]) = 1 := rfl

theorem scanSuccessor (R : Program 2) (bound seed candidate parameter : Nat) :
    evaluate (scan R) (ofFn ![bound+1,seed,candidate,parameter]) =
      if evaluate (scan R) (ofFn ![bound,seed,candidate,parameter]) = 1 ∧
        evaluate (positionTest R) (ofFn ![bound,seed,candidate,parameter]) = 1 then 1 else 0 := by
  change evaluate (scanStep R)
    (bound ::ᵥ evaluate (scan R) (bound ::ᵥ seed ::ᵥ candidate ::ᵥ parameter ::ᵥ nil) ::ᵥ
      seed ::ᵥ candidate ::ᵥ parameter ::ᵥ nil) = _
  rw [scanStep,conjunctionEvaluation]
  rfl

theorem scanAll (R : Program 2) (bound seed candidate parameter : Nat)
    (h : ∀ k < bound, evaluate (positionTest R) (ofFn ![k,seed,candidate,parameter]) = 1) :
    evaluate (scan R) (ofFn ![bound,seed,candidate,parameter]) = 1 := by
  induction bound with
  | zero => exact scanZero R seed candidate parameter
  | succ bound ih =>
    rw [scanSuccessor,if_pos ⟨ih (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self bound))),
      h bound (Nat.lt_succ_self bound)⟩]

theorem allTestsContext (R : Program 2) (context seed candidate : Nat) (Gamma : List Ty) :
    evaluate (allTests R) (ofFn ![seed,candidate,Nat.pair context (Encodable.encode Gamma)]) =
      evaluate (scan R) (ofFn ![Gamma.length,seed,candidate,Nat.pair context (Encodable.encode Gamma)]) := by
  change evaluate (scan R) (ofFn ![
    evaluate OriginalContextInsertion.length (ofFn ![
      evaluate (rightOf (.projection 2)) (ofFn ![seed,candidate,Nat.pair context (Encodable.encode Gamma)])]),
      seed,candidate,Nat.pair context (Encodable.encode Gamma)]) = _
  rw [rightOfEvaluation]
  simp only [evaluate,List.Vector.get_ofFn,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_zero,Matrix.cons_val_succ,Nat.unpair_pair]
  rw [OriginalContextInsertionCalibrationProof.lengthContext]

theorem classEvaluation (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (v : List.Vector Nat 3) :
    evaluate (classTest p H G W P) v =
      if (Nat.unpair (v.get 2)).2 = 0 then evaluate P v else
        if evaluate (OriginalActiveObservedClass.activation p H G W)
          (ofFn ![v.get 0,v.get 2]) = 0 then evaluate P v else
          if evaluate P v = 1 ∧ evaluate (allTests p.base.oldRepresentative) v = 1 then 1 else 0 := by
  rw [classTest,evalBranch,rightOfEvaluation,evalBranch,seedQueryEvaluation,conjunctionEvaluation]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeEvaluationProof
