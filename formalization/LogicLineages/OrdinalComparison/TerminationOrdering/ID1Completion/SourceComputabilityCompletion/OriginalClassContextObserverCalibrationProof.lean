module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverCalibrationProof
open Source InternalOriginalUniformParameterLeaves
open UniformCertificateCompletion
open OriginalClassContextObserver OriginalClassContextObserverEvaluationProof
open OriginalClassContextNativeDefinitions OriginalClassContextNativeProof
open OriginalActiveClassKernelCalibrationSupportProof
open OriginalActiveClassKernelEvaluationProof (activationAcceptance activationNonzero)
open OriginalContextExtensionCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem gammaEncoding (parameter : Nat) (Gamma : List Ty)
    (ho : ∀ value : Nat, parameterObject value parameter = some (Gamma,value)) :
    Encodable.encode Gamma = (Nat.unpair parameter).2 := by
  have h := (JointGammaDomainCodecProof.actualObjectCodec.2.1
    (Nat.pair (Nat.unpair parameter).2 0) (Gamma,0)).mp (ho 0)
  have he := congrArg (fun x : Nat => (Nat.unpair x).1) h
  simpa only [objectEncoding,Nat.unpair_pair] using he

theorem observerAccepted (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (hG : OriginalVariableLeaves.ContextGuardCalibrated n G)
    (hW : OriginalUniverseDecoder.HeadWindowCalibrated n arity W)
    (v : List.Vector Nat 3)
    (hnil : (Nat.unpair (v.get 2)).2 ≠ 0)
    (ha : evaluate (OriginalActiveObservedClass.activation p H G W)
      (ofFn ![v.get 0,v.get 2]) ≠ 0)
    (hit : OriginalTransparentMinimum.classValue n arity v = 1) :
    evaluate (observerTest p.base.oldRepresentative) v = 1 := by
  let q := OriginalTransparentDecoderSelection.transparentInputs H G W p
  have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
    (OriginalTransparentDecoderSelectionCalibrationProof.actualOriginalTransparentDecoderCalibration
      n arity p H G W hp hH hG hW).1
  have hactive := (activationAcceptance p H G W (v.get 0) (v.get 2)).mp
    (activationNonzero p H G W (v.get 0) (v.get 2) ha)
  have hwindow : GuardCalibration.validWindow n (Nat.unpair (v.get 2)).1 = 1 := by
    have hw : evaluate p.window (ofFn ![(Nat.unpair (v.get 2)).1]) = 1 := by
      simpa only [BottomRepresentativeEvaluationProof.windowAtEvaluation] using hactive.1
    have hc := hp.2.1 (ofFn ![(Nat.unpair (v.get 2)).1])
    change evaluate p.window (ofFn ![(Nat.unpair (v.get 2)).1]) =
      GuardCalibration.validWindow n (Nat.unpair (v.get 2)).1 at hc
    exact hc.symm.trans hw
  obtain ⟨ctx,hctx,hclosed⟩ :=
    (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 2)).1).1.mp hwindow
  obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma (v.get 2)
  have hgamma := gammaEncoding (v.get 2) Gamma ho
  cases Gamma with
  | nil => exact False.elim (hnil (by simpa using hgamma.symm))
  | cons sigma Gamma =>
    have hparameter : v.get 2 = Nat.pair (Nat.unpair (v.get 2)).1
        (Encodable.encode (sigma :: Gamma)) := by
      rw [hgamma,Nat.pair_unpair]
    have hseed := BottomRepresentativeEvaluationProof.decodedLeafSlice
      n arity q.base hq.1 (v.get 2) ctx hctx (sigma :: Gamma) ho (v.get 0)
    have hsource : InternalOriginalStepGuard.sourceValidityValue
        n arity ctx.1.1 ctx.1.2 (sigma :: Gamma) (v.get 0) = 1 :=
      hseed.1.symm.trans hactive.2
    have hclass : rawClassValue n arity ctx.1.1 ctx.1.2 (sigma :: Gamma)
        (v.get 0) (v.get 1) = 1 := by
      simpa only [OriginalTransparentMinimum.classValue,decodedValue,hctx,ho (v.get 0)] using hit
    have hobs := actualOriginalClassContextErasedObservers
      n arity ctx.1.1 ctx.1.2 Gamma sigma hclosed (v.get 0) (v.get 1) hsource hclass
    let parent := Nat.pair (Nat.unpair (v.get 2)).1 (Encodable.encode Gamma)
    have hparent : Encodable.decode (Nat.unpair parent).1 = some ctx := by
      simpa only [parent,Nat.unpair_pair] using hctx
    have hobject : ∀ value : Nat, parameterObject value parent = some (Gamma,value) := by
      intro value
      simp only [parameterObject,parent,Nat.unpair_pair]
      exact Encodable.encodek (Gamma,value)
    have hrep (value : Nat) := (BottomRepresentativeEvaluationProof.decodedLeafSlice
      n arity p.base hp.1 parent ctx hparent Gamma hobject value).2.2.1
    have hk : evaluate (erasedKey p.base.oldRepresentative) (ofFn ![v.get 0,v.get 2]) =
        evaluate (erasedKey p.base.oldRepresentative) (ofFn ![v.get 1,v.get 2]) := by
      conv_lhs => rw [hparameter]
      conv_rhs => rw [hparameter]
      rw [erasedKeySlice,erasedKeySlice]
      exact (hrep _).trans (hobs.2.2.1.trans (hrep _).symm)
    have hr : evaluate erasedRank (ofFn ![v.get 0,v.get 2]) =
        evaluate erasedRank (ofFn ![v.get 1,v.get 2]) := by
      conv_lhs => rw [hparameter]
      conv_rhs => rw [hparameter]
      rw [erasedRankSlice,erasedRankSlice]
      exact hobs.2.2.2
    rw [observerEvaluation,if_pos ⟨hk,hr⟩]

theorem actualOriginalClassContextObserverCalibration :
    OriginalClassContextObserverTargets.ActualOriginalClassContextObserverCalibration := by
  intro n arity p H G W P hp hH hG hW hP v
  rw [OriginalClassContextObserverEvaluationProof.classEvaluation]
  by_cases hnil : (Nat.unpair (v.get 2)).2 = 0
  · simp only [hnil,ite_true]
    exact hP v
  · simp only [hnil,ite_false]
    by_cases ha : evaluate (OriginalActiveObservedClass.activation p H G W)
        (ofFn ![v.get 0,v.get 2]) = 0
    · simp only [ha,ite_true]
      exact hP v
    · simp only [ha,ite_false,hP v]
      rcases OriginalActiveObservedCalibrationProof.classBoolean n arity v with hzero | hone
      · simp [hzero]
      · have ho := observerAccepted n arity p H G W hp hH hG hW v hnil ha hone
        simp [hone,ho]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverCalibrationProof
