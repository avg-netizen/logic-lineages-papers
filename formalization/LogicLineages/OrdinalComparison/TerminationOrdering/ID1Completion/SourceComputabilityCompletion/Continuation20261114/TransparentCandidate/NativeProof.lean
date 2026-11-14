module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.NativeProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedNumericDecoding
open NumberedLeastCodeRepresentative NumberedUniformPackedDecoding
open InternalOriginalUniformParameterLeaves
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem rawReencoding (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) :
    ((rawPackedDecode n arity Gamma value).map Encodable.encode).getD 0 =
      if (rawPackedDecode n arity Gamma value).isSome.toNat = 1 then value else 0 := by
  rw [NumberedUniformPackedDecodingProof.rawPackedCalibration]
  cases hd : decodePackedNumber n arity Gamma value with
  | none => simp [hd]
  | some q =>
    simp only [Option.map_some,Option.getD_some,Option.isSome_some,Bool.toNat_true,ite_true]
    change packedNumber q = value
    exact NumberedNumericDecodingProof.packedNumericSound n arity Gamma value q hd

theorem originalReencoding : Targets.OriginalReencoding := by
  intro n arity v
  obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma (v.get 1)
  simp only [candidateValue,targetValue,decodedValue,ho (v.get 0)]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 1)).1 with
  | none => simp [hc]
  | some ctx =>
    simp only [hc]
    exact rawReencoding n arity Gamma (v.get 0)

theorem targetBit (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) :
    targetValue n arity v = 0 ∨ targetValue n arity v = 1 := by
  obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma (v.get 1)
  simp only [targetValue,decodedValue,ho (v.get 0)]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 1)).1 with
  | none => simp [hc]
  | some ctx =>
    simp only [hc]
    cases rawPackedDecode n arity Gamma (v.get 0) <;> simp

theorem calibratedCandidate : Targets.CalibratedCandidate := by
  intro n arity H G hH hG v
  rw [candidate,InternalAcceptanceCalibrationProof.evalBranch,
    OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG,
    originalReencoding n arity v]
  change (if targetValue n arity v = 0 then 0 else v.get 0) = _
  rcases targetBit n arity v with h | h <;> simp [h]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.NativeProof
