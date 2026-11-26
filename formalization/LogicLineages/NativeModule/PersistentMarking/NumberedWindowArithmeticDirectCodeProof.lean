module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectWitnessCodeProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectMultisetChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectCodeProof
open NumberedWindowArithmeticFields NumberedWindowArithmeticFieldsProof
open NumberedWindowArithmeticDirectMultisetTargets NumberedWindowArithmeticDirectMultisetChecks
open NumberedWindowArithmeticDirectCode NumberedWindowArithmeticDirectCodeTargets
open NumberedWindowArithmeticDirectWitnessCodeProof

private theorem fieldsAt {xs : List Nat} {n : Nat} (h : encodeFields xs = n) :
    decodeFields n = some xs := by
  rw [← h]
  exact fieldsRound xs

theorem typed : ExactTypedAddressListOnCodes := by
  intro S K n hk
  constructor
  · intro h
    cases hCode : decodeFields n with
    | none => simp [typedAddressListCodeBit,hCode] at h
    | some xs =>
      have hx := (exact_TypedAddressListBit S K xs hk).mp
        (by simpa only [typedAddressListCodeBit,hCode] using h)
      exact ⟨xs,fieldsRead hCode,hx⟩
  · rintro ⟨xs,he,hx⟩
    simpa only [typedAddressListCodeBit,fieldsAt he] using
      (exact_TypedAddressListBit S K xs hk).mpr hx

theorem direct : ExactDirectMultisetOnCodes := by
  intro S K src dst hk
  constructor
  · rintro ⟨c,h⟩
    cases hs : decodeFields src with
    | none => simp [directMultisetCodeBit,hs] at h
    | some xs =>
      cases hw : decodeDirectWitness c with
      | none => simp [directMultisetCodeBit,hs,hw] at h
      | some w =>
        cases ht : decodeFields dst with
        | none => simp [directMultisetCodeBit,hs,hw,ht] at h
        | some ys =>
          have hStep := exact_SuppliedDirectMultisetSound S K xs ys w hk
            (by simpa only [directMultisetCodeBit,hs,hw,ht] using h)
          exact ⟨xs,ys,fieldsRead hs,fieldsRead ht,hStep⟩
  · rintro ⟨xs,ys,hs,ht,h⟩
    obtain ⟨w,hw⟩ := (exact_CertifiedDirectMultiset S K xs ys hk).mpr h
    exact ⟨encodeDirectWitness w,by
      simpa only [directMultisetCodeBit,fieldsAt hs,witnessRound w,fieldsAt ht] using hw⟩

theorem domains : OriginalCodedDirectDomains := by
  intro S K src dst h
  obtain ⟨xs,ys,hs,ht,hw⟩ := h
  exact ⟨⟨xs,hs,hw.1⟩,⟨ys,ht,hw.2.1⟩⟩

theorem malformed : CodedDirectRejectsMalformed := by
  constructor
  · intro S K src hs
    simp [typedAddressListCodeBit,hs]
  · intro S K src c dst h
    rcases h with hs | hw | ht
    · cases hw : decodeDirectWitness c <;> cases ht : decodeFields dst <;>
        simp [directMultisetCodeBit,hs,hw,ht]
    · cases hs : decodeFields src <;> cases ht : decodeFields dst <;>
        simp [directMultisetCodeBit,hs,hw,ht]
    · cases hs : decodeFields src <;> cases hw : decodeDirectWitness c <;>
        simp [directMultisetCodeBit,hs,hw,ht]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectCodeProof
