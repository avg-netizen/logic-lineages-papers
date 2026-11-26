module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeSelectorsProof
open Source NumberedLeastCodeRepresentative
open OriginalClassContextAllPositionObserver
open OriginalContextInsertionCalibrationProof OriginalContextExtensionCalibrationProof
open InternalRawListRecursionEvaluationProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

 theorem dropPrefix (binders Gamma : List Ty) :
    evaluate InternalRawListRecursion.drop (ofFn ![binders.length,Encodable.encode (binders ++ Gamma)]) =
      Encodable.encode Gamma := by
  induction binders with
  | nil => rfl
  | cons sigma binders ih =>
    simp only [List.length_cons,List.cons_append,contextEncoding]
    simp only [InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one] at ih ⊢
    rw [show Nat.succ (Nat.pair (typeNumber sigma) (Encodable.encode (binders ++ Gamma))) =
      1 + Nat.pair (typeNumber sigma) (Encodable.encode (binders ++ Gamma)) by omega,dropCons]
    exact ih

theorem lookupPrefix (binders Gamma : List Ty) (sigma : Ty) :
    evaluate InternalRawListRecursion.lookup
      (ofFn ![binders.length,Encodable.encode (binders ++ sigma :: Gamma)]) = typeNumber sigma := by
  simp only [InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one,lookupEvaluation]
  have hd := dropPrefix binders (sigma :: Gamma)
  simp only [InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one] at hd
  rw [hd,contextEncoding]
  simp only [Nat.succ_sub_one,Nat.unpair_pair]

theorem frontZero (code : Nat) : evaluate front (ofFn ![0,code]) = 0 := rfl

theorem frontSuccessor (k code : Nat) :
    evaluate front (ofFn ![k+1,code]) =
      evaluate InternalApplicationValidityStackAppend.append
        (ofFn ![evaluate front (ofFn ![k,code]),
          evaluate InternalListCodec.consCode
            (ofFn ![evaluate InternalRawListRecursion.lookup (ofFn ![k,code]),0])]) := by
  change evaluate frontStep (k ::ᵥ evaluate front (k ::ᵥ code ::ᵥ nil) ::ᵥ code ::ᵥ nil) = _
  simp only [frontStep,evaluate,List.Vector.get_ofFn,List.Vector.get_cons_zero,List.Vector.get_cons_succ,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,InternalAcceptance.constantZero]
  rfl

/-- Exact forward prefix in the ORIGINAL Encodable context, not reverse. -/
theorem frontPrefix (binders Gamma : List Ty) :
    evaluate front (ofFn ![binders.length,Encodable.encode (binders ++ Gamma)]) = Encodable.encode binders := by
  induction binders using List.reverseRecOn generalizing Gamma with
  | nil => rfl
  | append_singleton binders sigma ih =>
    simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append]
    rw [frontSuccessor,ih (sigma :: Gamma),lookupPrefix binders Gamma sigma]
    have hcons : evaluate InternalListCodec.consCode (ofFn ![typeNumber sigma,0]) = Encodable.encode [sigma] := by
      simpa using actualOriginalContextConsCalibration sigma []
    rw [hcons]
    exact appendContext binders [sigma]

theorem deletePrefix (binders Gamma : List Ty) (sigma : Ty) :
    evaluate deleteAt (ofFn ![binders.length,Encodable.encode (binders ++ sigma :: Gamma)]) =
      Encodable.encode (binders ++ Gamma) := by
  change evaluate InternalApplicationValidityStackAppend.append
    (ofFn ![evaluate front (ofFn ![binders.length,Encodable.encode (binders ++ sigma :: Gamma)]),
      evaluate InternalRawListRecursion.drop (ofFn ![binders.length+1,Encodable.encode (binders ++ sigma :: Gamma)])]) = _
  rw [frontPrefix]
  have hd := dropPrefix (binders ++ [sigma]) Gamma
  simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] at hd
  rw [hd,appendContext]

theorem erasedPackedSlice (context value : Nat) (binders Gamma : List Ty) (sigma : Ty) :
    evaluate erasedPacked (ofFn ![binders.length,value,Nat.pair context (Encodable.encode (binders ++ sigma :: Gamma))]) =
      OriginalClassContextPrefixNative.erasedPacked binders sigma value := by
  change evaluate OriginalRawSyntaxTransport.erasePackedRaw
    (ofFn ![evaluate InternalRawListRecursion.lookup
      (ofFn ![binders.length, evaluate (InternalApplicationCertificateConstructors.rightOf (.projection 2))
        (ofFn ![binders.length,value,Nat.pair context (Encodable.encode (binders ++ sigma :: Gamma))])]),binders.length,value]) = _
  rw [rightOfEvaluation]
  simp only [evaluate,List.Vector.get_ofFn,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_zero,Matrix.cons_val_succ,Nat.unpair_pair]
  rw [lookupPrefix]
  rfl

theorem erasedParameterSlice (context value : Nat) (binders Gamma : List Ty) (sigma : Ty) :
    evaluate erasedParameter (ofFn ![binders.length,value,Nat.pair context (Encodable.encode (binders ++ sigma :: Gamma))]) =
      Nat.pair context (Encodable.encode (binders ++ Gamma)) := by
  rw [erasedParameter,pairOfEvaluation]
  have hleft : evaluate (InternalApplicationCertificateConstructors.leftOf (.projection 2))
      (ofFn ![binders.length,value,Nat.pair context (Encodable.encode (binders ++ sigma :: Gamma))]) = context := by
    rw [leftOfEvaluation]
    simp only [evaluate,List.Vector.get_ofFn,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Nat.unpair_pair]
  rw [hleft]
  change Nat.pair context (evaluate deleteAt
    (ofFn ![binders.length,evaluate (InternalApplicationCertificateConstructors.rightOf (.projection 2))
      (ofFn ![binders.length,value,Nat.pair context (Encodable.encode (binders ++ sigma :: Gamma))])])) = _
  rw [rightOfEvaluation]
  simp only [evaluate,List.Vector.get_ofFn,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Nat.unpair_pair]
  rw [deletePrefix]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeSelectorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeSelectorsProof
