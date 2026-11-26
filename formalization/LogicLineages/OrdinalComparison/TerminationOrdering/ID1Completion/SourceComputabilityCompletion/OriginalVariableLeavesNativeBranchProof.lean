module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesNativeBranchProof
open Source NumberedLeastCodeRepresentative NumberedAuxiliaryDecoding
open OriginalVariableLeaves OriginalVariableLeavesCodecProof OriginalVariableLeavesEvaluationProof
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalOriginalUniformParameterLeaves
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- ALL raw variable-tag inputs. The original outer Context may fail to
decode; the exact source and target outputs then remain zero. -/
theorem variableBranchesEqual (n : Nat) (arity : Fin n → Nat)
    (guard : Program 1) (data : Data) (hg : ContextGuardCalibrated n guard)
    (hc : Calibrated n arity data) (raw parameter : Nat)
    (htag : (Nat.unpair (Nat.unpair raw).2).1 = 0) :
    evaluate (sourceVariable data.member) (List.Vector.ofFn ![raw,parameter]) =
        evaluate data.oldSource (List.Vector.ofFn ![raw,parameter]) ∧
    evaluate (targetVariable guard) (List.Vector.ofFn ![raw,parameter]) =
        evaluate data.oldTarget (List.Vector.ofFn ![raw,parameter]) := by
  let v := List.Vector.ofFn ![raw,parameter]
  obtain ⟨tau,ht,hraw⟩ := variableRawShape raw htag
  obtain ⟨Gamma,hGamma,ho⟩ := parameterGammaCode parameter
  let index := (Nat.unpair (Nat.unpair raw).2).2
  have hv : evaluate variableCheck v = (decodeVariable Gamma tau index).isSome.toNat := by
    rw [variableCheckEvaluation]
    change evaluate OriginalVariableDecoder.check
      (List.Vector.ofFn ![(Nat.unpair raw).1,index,(Nat.unpair parameter).2]) = _
    rw [← ht,← hGamma]
    exact OriginalVariableDecoderEvaluationProof.actualOriginalVariableDecoderCalibration Gamma tau index
  have hq := contextCheckEvaluation n guard hg v
  have hm := typeMemberEvaluation n arity data hc v
  change evaluate (typeMember data.member) v =
    memberValue n (List.Vector.ofFn ![(Nat.unpair raw).1,parameter]) at hm
  rw [← ht] at hm
  cases hctx : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair parameter).1 with
  | none =>
    have hm0 : evaluate (typeMember data.member) v = 0 := by
      rw [hm]
      simp only [memberValue,decodedValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
        Matrix.cons_val_one,hctx]
    have hq0 : evaluate (contextCheck guard) v = 0 := by
      simpa only [v,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,hctx,
        Option.isSome_none,Bool.toNat_false] using hq
    have hs0 : evaluate data.oldSource v = 0 := by
      rw [hc.1]
      simp only [sourceValue,decodedValue,v,List.Vector.get_ofFn,Matrix.cons_val_zero,
        Matrix.cons_val_one,hctx]
    have ht0 : evaluate data.oldTarget v = 0 := by
      rw [hc.2.1]
      simp only [targetValue,decodedValue,v,List.Vector.get_ofFn,Matrix.cons_val_zero,
        Matrix.cons_val_one,hctx]
    change evaluate (sourceVariable data.member) v = evaluate data.oldSource v ∧
      evaluate (targetVariable guard) v = evaluate data.oldTarget v
    rw [sourceVariable,targetVariable,actualConjunctionEvaluation,actualConjunctionEvaluation,
      hm0,hq0,hs0,ht0]
    simp
  | some ctx =>
    have hm1 : evaluate (typeMember data.member) v = (decide (tau ∈ ctx.1.2)).toNat := by
      rw [hm]
      simp only [memberValue,decodedValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
        Matrix.cons_val_one,hctx,ho,InternalStructuralEndpointGuard.membershipValue,
        NumberedNumericDecodingSupportProof.typeRoundTrip]
    have hq1 : evaluate (contextCheck guard) v = 1 := by
      simpa only [v,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,hctx,
        Option.isSome_some,Bool.toNat_true] using hq
    have hs := BottomRepresentativeEvaluationProof.decodedLeafSlice
      n arity data hc parameter ctx hctx Gamma ho raw
    have hsource : evaluate data.oldSource v =
        ((decide (tau ∈ ctx.1.2)) && (decodeVariable Gamma tau index).isSome).toNat := by
      rw [hs.1,hraw,variableSourceValue]
    have htarget : evaluate data.oldTarget v = (decodeVariable Gamma tau index).isSome.toNat := by
      rw [hs.2.1,hraw,variableTargetValue]
    change evaluate (sourceVariable data.member) v = evaluate data.oldSource v ∧
      evaluate (targetVariable guard) v = evaluate data.oldTarget v
    rw [sourceVariable,targetVariable,actualConjunctionEvaluation,actualConjunctionEvaluation,
      hm1,hq1,hv,hsource,htarget]
    cases hm : decide (tau ∈ ctx.1.2) <;>
      cases hv : (decodeVariable Gamma tau index).isSome <;> simp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesNativeBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesNativeBranchProof
