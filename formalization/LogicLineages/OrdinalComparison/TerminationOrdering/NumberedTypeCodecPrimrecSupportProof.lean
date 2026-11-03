module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecSupportProof
open Source NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedMultisetNumeric NumberedTypeCodecPrimrec

theorem typeTo : Primrec typeEquiv := Primrec.of_equiv
theorem typeFrom : Primrec typeEquiv.symm := Primrec.of_equiv_symm

theorem decodeTypeExact (value : Nat) : decodeType value=some (typeEquiv.symm value) := by
  obtain ⟨tau,h,he⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal value
  simp [typeEquiv,typeFromNumber,h]

theorem listCodeExact (types : List Ty) : typesNumber types=numbersNumber (types.map typeEquiv) := by
  induction types with
  | nil => rfl
  | cons tau types ih => simp [typesNumber,numbersNumber,ih,typeEquiv]

theorem parserCalibration (fuel : Nat) : ∀ value, typesParse fuel value =
    (numbersParse fuel value).map (List.map typeEquiv.symm) := by
  induction fuel with
  | zero => intro value; rfl
  | succ fuel ih =>
    intro value
    cases value with
    | zero => rfl
    | succ value =>
      simp [typesParse,numbersParse,decodeTypeExact,ih,Option.map_eq_bind,Option.bind_assoc]

theorem decoderCalibration (value : Nat) : decodeTypes value=
    (decodeNumbers value).map (List.map typeEquiv.symm) := by
  unfold decodeTypes
  rw [parserCalibration]
  cases h : numbersParse (value+1) value with
  | none => simp [decodeNumbers,h]
  | some xs =>
    have he := NumberedMultisetNumericSupportProof.numbersParseSound (value+1) value xs h
    have hc : typesNumber (xs.map typeEquiv.symm)=value := by
      rw [listCodeExact]
      simpa using he
    simp [decodeNumbers,h,hc]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecSupportProof
