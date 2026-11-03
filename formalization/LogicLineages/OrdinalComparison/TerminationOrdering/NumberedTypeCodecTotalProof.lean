module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalProof
open Source NumberedLeastCodeRepresentative NumberedNumericDecoding

theorem typeParserTotal : NumberedTypeCodecTotalTargets.ActualTypeParserTotal := by
  intro fuel
  induction fuel with
  | zero => intro value h; omega
  | succ fuel ih =>
    intro value h
    cases value with
    | zero => exact ⟨.ground,rfl,rfl⟩
    | succ value =>
      have hl := Nat.left_le_pair (Nat.unpair value).1 (Nat.unpair value).2
      have hr := Nat.right_le_pair (Nat.unpair value).1 (Nat.unpair value).2
      rw [Nat.pair_unpair] at hl hr
      obtain ⟨sigma,hs,es⟩ := ih (Nat.unpair value).1 (by omega)
      obtain ⟨tau,ht,et⟩ := ih (Nat.unpair value).2 (by omega)
      refine ⟨.arrow sigma tau,?_,?_⟩
      · simp [typeParse,hs,ht]
      · simp [typeNumber,es,et,Nat.add_comm]

theorem typeDecoderTotal : NumberedTypeCodecTotalTargets.ActualTypeDecoderTotal := by
  intro value
  obtain ⟨tau,ht,he⟩ := typeParserTotal (value+1) value (by omega)
  exact ⟨tau,by simp [decodeType,ht,he],he⟩

theorem typeCodeBijection : NumberedTypeCodecTotalTargets.ActualTypeCodeBijection := by
  refine ⟨NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective,?_⟩
  intro value
  obtain ⟨tau,_,he⟩ := typeDecoderTotal value
  exact ⟨tau,he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalProof
