module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEvaluationProof
open Source NumberedLeastCodeRepresentative NumberedAuxiliaryDecoding
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalVariableDecoder
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo vectorThree exactEqualityEvaluation)
open InternalRawListRecursionEvaluationProof
open InternalAcceptanceCalibrationProof

attribute [local irreducible] InternalRawListRecursion.drop InternalListCodec.headCode
  InternalEqualityTest.equalityTest

theorem restEvaluation (typ index gamma : Nat) :
    evaluate rest (typ ::ᵥ index ::ᵥ gamma ::ᵥ List.Vector.nil) =
      evaluate InternalRawListRecursion.drop (index ::ᵥ gamma ::ᵥ List.Vector.nil) := by
  change evaluate InternalRawListRecursion.drop (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((Fin.cons (.projection 1) (Fin.cons (.projection 2) Fin.elim0) :
      Fin 2 → Program 3) i) (typ ::ᵥ index ::ᵥ gamma ::ᵥ List.Vector.nil)) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo]
  rfl

theorem headEvaluation (typ index gamma : Nat) :
    evaluate head (typ ::ᵥ index ::ᵥ gamma ::ᵥ List.Vector.nil) =
      (Nat.unpair (evaluate InternalRawListRecursion.drop
        (index ::ᵥ gamma ::ᵥ List.Vector.nil) - 1)).1 := by
  change evaluate InternalListCodec.headCode (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate rest (typ ::ᵥ index ::ᵥ gamma ::ᵥ List.Vector.nil)) = _
  rw [vectorOne,InternalListCodecEvaluationProof.headEvaluation,restEvaluation]

theorem matchesEvaluation (typ index gamma : Nat) :
    evaluate matchesType (typ ::ᵥ index ::ᵥ gamma ::ᵥ List.Vector.nil) =
      if typ = (Nat.unpair (evaluate InternalRawListRecursion.drop
        (index ::ᵥ gamma ::ᵥ List.Vector.nil) - 1)).1 then 1 else 0 := by
  change evaluate InternalEqualityTest.equalityTest (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((Fin.cons (.projection 0) (Fin.cons head Fin.elim0) :
      Fin 2 → Program 3) i) (typ ::ᵥ index ::ᵥ gamma ::ᵥ List.Vector.nil)) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo]
  change evaluate InternalEqualityTest.equalityTest
    (typ ::ᵥ evaluate head (typ ::ᵥ index ::ᵥ gamma ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) = _
  rw [exactEqualityEvaluation,headEvaluation]

theorem checkEvaluation (typ index gamma : Nat) :
    evaluate check (typ ::ᵥ index ::ᵥ gamma ::ᵥ List.Vector.nil) =
      if evaluate InternalRawListRecursion.drop (index ::ᵥ gamma ::ᵥ List.Vector.nil) = 0 then 0
      else if typ = (Nat.unpair (evaluate InternalRawListRecursion.drop
        (index ::ᵥ gamma ::ᵥ List.Vector.nil) - 1)).1 then 1 else 0 := by
  rw [check,evalBranch,restEvaluation,matchesEvaluation]
  rfl

theorem dropNil (index : Nat) :
    evaluate InternalRawListRecursion.drop (index ::ᵥ 0 ::ᵥ List.Vector.nil) = 0 := by
  induction index with
  | zero => exact dropZero 0
  | succ index ih => rw [dropSuccessor,ih]; rfl

theorem checkNil (typ index : Nat) :
    evaluate check (typ ::ᵥ index ::ᵥ 0 ::ᵥ List.Vector.nil) = 0 := by
  rw [checkEvaluation,dropNil]
  rfl

theorem checkConsZero (typ head tail : Nat) :
    evaluate check (typ ::ᵥ 0 ::ᵥ (1 + Nat.pair head tail) ::ᵥ List.Vector.nil) =
      if typ = head then 1 else 0 := by
  rw [checkEvaluation,dropZero]
  simp [Nat.add_comm 1]

theorem checkConsSuccessor (typ index head tail : Nat) :
    evaluate check (typ ::ᵥ (index+1) ::ᵥ (1 + Nat.pair head tail) ::ᵥ List.Vector.nil) =
      evaluate check (typ ::ᵥ index ::ᵥ tail ::ᵥ List.Vector.nil) := by
  rw [checkEvaluation,dropCons,checkEvaluation]

theorem calibration (Gamma : List Ty) (tau : Ty) (index : Nat) :
    evaluate check (typeNumber tau ::ᵥ index ::ᵥ Encodable.encode Gamma ::ᵥ List.Vector.nil) =
      (decodeVariable Gamma tau index).isSome.toNat := by
  induction Gamma generalizing index with
  | nil =>
    rw [Encodable.encode_list_nil,checkNil]
    cases index <;> rfl
  | cons sigma Gamma ih =>
    rw [OriginalContextExtensionCalibrationProof.contextEncoding]
    rw [show Nat.succ (Nat.pair (typeNumber sigma) (Encodable.encode Gamma)) =
      1 + Nat.pair (typeNumber sigma) (Encodable.encode Gamma) by omega]
    cases index with
    | zero =>
      rw [checkConsZero]
      by_cases h : sigma = tau
      · subst sigma
        simp [decodeVariable]
      · have hn : typeNumber tau ≠ typeNumber sigma := by
          intro he
          exact h (NumberedTypeCodecPrimrec.typeEquiv.injective he).symm
        simp [decodeVariable,h,hn]
    | succ index =>
      rw [checkConsSuccessor,decodeVariable,Option.isSome_map]
      exact ih index

theorem actualOriginalVariableDecoderCalibration :
    OriginalVariableDecoderTargets.ActualOriginalVariableDecoderCalibration := by
  intro Gamma tau index
  rw [vectorThree]
  exact calibration Gamma tau index

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEvaluationProof
