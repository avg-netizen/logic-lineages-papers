module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTyCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderCodeProof
open NumberedWindowArithmeticPair (pair decode)
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticBinderCode
open NumberedWindowArithmeticAtomCodeTargets NumberedWindowArithmeticCodecLaws

private theorem zeroRead (fuel : Nat) (Γ : List Ty) (h : decodeBindersFuel fuel 0 = some Γ) :
    encodeBinders Γ = 0 := by
  have e : ([] : List Ty) = Γ :=
    Option.some.inj (by cases fuel <;> simpa [decodeBindersFuel] using h)
  subst Γ
  rfl

theorem sound (fuel code : Nat) (Γ : List Ty) (h : decodeBindersFuel fuel code = some Γ) :
    encodeBinders Γ = code := by
  induction fuel generalizing code Γ with
  | zero =>
    cases code with
    | zero => exact zeroRead 0 Γ h
    | succ code => simp [decodeBindersFuel] at h
  | succ fuel ih =>
    cases code with
    | zero => exact zeroRead (fuel+1) Γ h
    | succ code =>
      cases hp : decode code with
      | none => simp [decodeBindersFuel,hp] at h
      | some pr =>
        obtain ⟨a,b⟩ := pr
        cases ha : decodeTy a with
        | none => simp [decodeBindersFuel,hp,ha] at h
        | some A =>
          cases hb : decodeBindersFuel fuel b with
          | none => simp [decodeBindersFuel,hp,ha,hb] at h
          | some B =>
            have e : A :: B = Γ :=
              Option.some.inj (by simpa [decodeBindersFuel,hp,ha,hb] using h)
            subst Γ
            simp only [encodeBinders,NumberedWindowArithmeticTyCodeProof.decodeSound ha,
              ih b B hb,pairRead hp]

theorem complete (fuel : Nat) (Γ : List Ty) (h : encodeBinders Γ ≤ fuel) :
    decodeBindersFuel fuel (encodeBinders Γ) = some Γ := by
  induction Γ generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons σ Γ ih =>
    cases fuel with
    | zero => simp [encodeBinders] at h
    | succ f =>
      have hr : pair (encodeTy σ) (encodeBinders Γ) ≤ f := Nat.le_of_succ_le_succ h
      have hb := (pairBounds (encodeTy σ) (encodeBinders Γ)).2
      have ht := ih f (Nat.le_trans hb hr)
      simp [encodeBinders,decodeBindersFuel,pairRound,
        NumberedWindowArithmeticTyCodeProof.roundtrip,ht]

theorem calibration : BinderFuelCalibration := ⟨sound,complete⟩

theorem roundtrip (Γ : List Ty) : decodeBinders (encodeBinders Γ) = some Γ :=
  complete (encodeBinders Γ) Γ (Nat.le_refl _)

theorem decodeSound {n : Nat} {Γ : List Ty} (h : decodeBinders n = some Γ) :
    encodeBinders Γ = n := sound n n Γ h

theorem exactCodec : ExactBinderCodec :=
  codec encodeBinders decodeBinders (fun _ _ h => decodeSound h) roundtrip

end LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderCodeProof
