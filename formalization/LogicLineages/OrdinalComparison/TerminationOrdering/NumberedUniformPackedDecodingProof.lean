module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingProof
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open NumberedUniformPackedDecoding

theorem rawStructuralCalibration :
    NumberedUniformPackedDecodingTargets.ActualRawStructuralCalibration := by
  intro n arity Gamma raw
  rcases raw with ⟨tau,code⟩
  cases h : decodeTerm arity Gamma tau code with
  | none => simp [rawStructuralDecode, decodePacked, h]
  | some q =>
    have hc := NumberedAuxiliaryDecodingProof.termDecodeSound (Fin n) arity Gamma tau code q h
    simp [rawStructuralDecode, decodePacked, h, packedCode, hc]

theorem rawStructuralDecoderPrimitive :
    NumberedUniformPackedDecodingTargets.ActualRawStructuralDecoderPrimitive := by
  intro n arity
  exact Primrec.cond (NumberedTypedValidityPrimrecProof.termSuccessPrimitive n arity)
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)

theorem rawPackedCalibration :
    NumberedUniformPackedDecodingTargets.ActualRawPackedCalibration := by
  intro n arity Gamma value
  cases h : decodePackedNumber n arity Gamma value with
  | none => simp [rawPackedDecode, h]
  | some q =>
    have hv := NumberedNumericDecodingProof.packedNumericSound n arity Gamma value q h
    rw [← hv]
    unfold rawPackedDecode
    rw [NumberedNumericDecodingProof.packedNumericRoundTrip]
    simp [packedNumber, NumberedNumericDecodingSupportProof.typeRoundTrip,
      NumberedNumericDecodingProof.codeRoundTrip, packedCode]

theorem rawPackedDecoderPrimitive :
    NumberedUniformPackedDecodingTargets.ActualRawPackedDecoderPrimitive := by
  intro n arity
  have hparse : Primrec (fun value : Nat =>
      (decodeType (Nat.unpair value).1).bind (fun tau =>
        (decodeCode n (Nat.unpair value).2).map (fun code => (tau,code)))) := by
    apply Primrec.option_bind
      (g := fun value tau => (decodeCode n (Nat.unpair value).2).map
        (fun code => (tau,code)))
      (NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp (Primrec.fst.comp Primrec.unpair))
    apply Primrec.option_map
      (g := fun (p : Nat × Ty) (code : Code (Fin n)) => (p.2,code))
      ((NumberedCodeCodecPrimrecProof.codeDecoderPrimitive n).comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
    exact ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  have h := Primrec.cond (NumberedTypedValidityPrimrecProof.numericPackedSuccessPrimitive n arity)
    (hparse.comp Primrec.snd) (Primrec.const none)
  exact h.of_eq (by
    intro p
    simp only [rawPackedDecode, Option.map_eq_bind, Option.pure_def]
    rfl)

theorem rawUniverseCalibration :
    NumberedUniformPackedDecodingTargets.ActualRawUniverseCalibration := by
  intro n arity symbols S Gamma value
  rw [rawUniverseDecode, rawPackedCalibration]
  unfold rawCarrierTest decodeUniverse
  cases h : decodePackedNumber n arity Gamma value with
  | none => rfl
  | some q => cases hu : universeTest symbols S q.2 <;> simp [hu, Option.filter]

theorem rawUniverseDecoderPrimitive :
    NumberedUniformPackedDecodingTargets.ActualRawUniverseDecoderPrimitive := by
  intro n arity
  exact Primrec.cond (NumberedUniversePrimrecProof.rawCarrierPrimitive n arity)
    ((rawPackedDecoderPrimitive n arity).comp Primrec.snd) (Primrec.const none)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingProof
