module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrec
open Source NumberedLeastCodeRepresentative NumberedNumericDecoding

def typeFromNumber (value : Nat) : Ty :=
  (decodeType value).get (by
    obtain ⟨tau,h,_⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal value
    simp [h])

def typeEquiv : Ty ≃ Nat where
  toFun := typeNumber
  invFun := typeFromNumber
  left_inv tau := by
    have h := NumberedNumericDecodingSupportProof.typeRoundTrip tau
    simp [typeFromNumber,h]
  right_inv value := by
    obtain ⟨tau,h,he⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal value
    simpa [typeFromNumber,h] using he

instance typePrimcodable : Primcodable Ty := Primcodable.ofEquiv Nat typeEquiv

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrec
