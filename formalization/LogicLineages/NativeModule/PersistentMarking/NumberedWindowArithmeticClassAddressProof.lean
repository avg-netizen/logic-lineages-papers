module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRawHopCodeProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticBinderCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextTargets

private theorem assembleSound (tag : Nat) (fs : List Nat) (a : ClassAddress)
    (h : assembleAddress tag fs = some a) : encodeAddress a = encodeNode tag fs := by
  unfold assembleAddress at h
  split at h
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨Γ,hΓ,τ,hτ,rfl⟩ := h
    simp only [encodeAddress,NumberedWindowArithmeticBinderCodeProof.decodeSound hΓ,
      NumberedWindowArithmeticTyCodeProof.decodeSound hτ]
  · cases h

theorem read {n : Nat} {a : ClassAddress} (h : decodeAddress n = some a) :
    encodeAddress a = n :=
  NumberedWindowArithmeticRawHopCodeProof.taggedSound
    encodeAddress assembleAddress assembleSound n a h

theorem round (a : ClassAddress) : decodeAddress (encodeAddress a) = some a := by
  cases a
  simp [encodeAddress,decodeAddress,nodeRound,assembleAddress,
    NumberedWindowArithmeticBinderCodeProof.roundtrip,NumberedWindowArithmeticTyCodeProof.roundtrip]

theorem atCode {n : Nat} {a : ClassAddress} (h : encodeAddress a = n) :
    decodeAddress n = some a := by
  rw [← h]
  exact round a

theorem exactCodec : ExactClassAddressCodec :=
  NumberedWindowArithmeticCodecLaws.codec encodeAddress decodeAddress (fun _ _ => read) round

end LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddressProof
