module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedCalibrationProof
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedNumericDecoding NumberedUniformPackedDecoding
open InternalOriginalUniformParameterLeaves OriginalTransparentMinimum
open OriginalRawSyntaxTransport OriginalActiveObservedClass
open OriginalRankGuardedRepresentativeEvaluationProof (packedRank)
open InternalAcceptanceCalibrationProof InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem classNumberRank (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hc : SubtypeClosed (fun tau => tau ∈ S))
    (q : Packed (Fin n) arity Gamma) (value : Nat)
    (hit : ContextUniformPrimary.classNumberTest arity symbols S Gamma
      (NumberedAuxiliaryCoding.packedCode q) value = true) :
    evaluate variableRankPackedRaw (ofFn ![value]) =
      evaluate variableRankPackedRaw (ofFn ![packedNumber q]) := by
  rw [ContextUniformPrimaryCalibrationProof.classNumberTestCalibration] at hit
  cases hd : decodePackedNumber n arity Gamma value with
  | none => simp [NumberedRepresentativePrimrec.classNumberTest,hd] at hit
  | some r =>
    have hr : r ∈ NumberedFinitePrimaryClass.primaryClass symbols S q := by
      simpa [NumberedRepresentativePrimrec.classNumberTest,hd,
        NumberedFinitePrimaryClass.primaryTest] using hit
    have primary := NumberedFinitePrimaryClassProof.reachableSound symbols S hc q _ r hr
    rw [← NumberedNumericDecodingProof.packedNumericSound n arity Gamma value r hd,
      packedRank,packedRank]
    exact (NumberedVariableCountProof.actualPrimaryVariableCount
      (Fin n) arity symbols S Gamma q r primary).symm

theorem rawClassRank (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hc : SubtypeClosed (fun tau => tau ∈ S))
    (seed candidate : Nat)
    (hit : ((rawPackedDecode n arity Gamma seed).any
      (fun q => ContextUniformPrimary.classNumberTest arity symbols S Gamma q candidate)).toNat = 1) :
    evaluate variableRankPackedRaw (ofFn ![candidate]) =
      evaluate variableRankPackedRaw (ofFn ![seed]) := by
  rw [NumberedUniformPackedDecodingProof.rawPackedCalibration] at hit
  cases hd : decodePackedNumber n arity Gamma seed with
  | none => simp [hd] at hit
  | some q =>
    have hb : ContextUniformPrimary.classNumberTest arity symbols S Gamma
        (NumberedAuxiliaryCoding.packedCode q) candidate = true := by
      simpa [hd] using hit
    rw [← NumberedNumericDecodingProof.packedNumericSound n arity Gamma seed q hd]
    exact classNumberRank n arity symbols S Gamma hc q candidate hb

theorem classBoolean (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3) :
    classValue n arity v = 0 ∨ classValue n arity v = 1 := by
  obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma (v.get 2)
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 2)).1 with
  | none => simp [classValue,decodedValue,hc]
  | some ctx =>
    simp only [classValue,decodedValue,hc,ho (v.get 0)]
    cases hb : (rawPackedDecode n arity Gamma (v.get 0)).any
        (fun q => ContextUniformPrimary.classNumberTest arity ctx.1.1 ctx.1.2 Gamma q (v.get 1)) <;>
      simp [hb]

theorem classRankAtWindow (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3)
    (hw : GuardCalibration.validWindow n (Nat.unpair (v.get 2)).1 = 1)
    (hit : classValue n arity v = 1) :
    evaluate variableRankPackedRaw (ofFn ![v.get 1]) =
      evaluate variableRankPackedRaw (ofFn ![v.get 0]) := by
  obtain ⟨ctx,hctx,hclosed⟩ :=
    (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 2)).1).1.mp hw
  obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma (v.get 2)
  simp only [classValue,decodedValue,hctx,ho (v.get 0)] at hit
  exact rawClassRank n arity ctx.1.1 ctx.1.2 Gamma hclosed (v.get 0) (v.get 1) hit

theorem observedRankSame (v : List.Vector Nat 3)
    (he : evaluate variableRankPackedRaw (ofFn ![v.get 1]) =
      evaluate variableRankPackedRaw (ofFn ![v.get 0])) :
    evaluate (InternalApplicationStepPeel.same
      (.composition variableRankPackedRaw (fun _ : Fin 1 => (.projection 1 : Program 3)))
      (.composition variableRankPackedRaw (fun _ : Fin 1 => (.projection 0 : Program 3)))) v = 1 := by
  rw [sameEvaluation]
  change (if evaluate variableRankPackedRaw (ofFn fun _ : Fin 1 => v.get 1) =
    evaluate variableRankPackedRaw (ofFn fun _ : Fin 1 => v.get 0) then 1 else 0) = 1
  simpa only [InternalEqualityTestEvaluationProof.vectorOne,Matrix.cons_val_zero] using
    (if_pos he : (if evaluate variableRankPackedRaw (ofFn ![v.get 1]) =
      evaluate variableRankPackedRaw (ofFn ![v.get 0]) then 1 else 0) = 1)

theorem actualOriginalActiveObservedRankCalibration :
    OriginalActiveObservedCalibrationTargets.ActualOriginalActiveObservedRankCalibration := by
  intro n arity p H G W P hwindow hP v
  rw [classTest,evalBranch]
  change (if evaluate (activation p H G W) (ofFn ![v.get 0,v.get 2]) = 0
    then evaluate P v else evaluate (OriginalObservedClass.observed variableRankPackedRaw P) v) = _
  by_cases ha : evaluate (activation p H G W) (ofFn ![v.get 0,v.get 2]) = 0
  · simp only [ha,ite_true]
    exact hP v
  · simp only [ha,ite_false]
    have hactive : evaluate (BottomRepresentative.windowAt p.window) (ofFn ![v.get 0,v.get 2]) = 1 ∧
        evaluate (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource
          (ofFn ![v.get 0,v.get 2]) = 1 := by
      by_contra hn
      apply ha
      change evaluate (OriginalRankGuardedRepresentative.active
        (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource p.window)
        (ofFn ![v.get 0,v.get 2]) = 0
      rw [OriginalRankGuardedRepresentative.active,conjunctionEvaluation]
      exact if_neg hn
    have hw : GuardCalibration.validWindow n (Nat.unpair (v.get 2)).1 = 1 := by
      simpa only [BottomRepresentativeEvaluationProof.windowAtEvaluation,hwindow,
        GuardCalibration.validWindowValue,List.Vector.get_ofFn,Matrix.cons_val_zero] using hactive.1
    rcases classBoolean n arity v with hzero | hone
    · rw [OriginalObservedClass.observed,conjunctionEvaluation,hP,hzero]
      simp [hzero]
    · have hs := observedRankSame v (classRankAtWindow n arity v hw hone)
      rw [OriginalObservedClass.observed,conjunctionEvaluation,hP,hone,hs]
      simp [hone]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedCalibrationProof
