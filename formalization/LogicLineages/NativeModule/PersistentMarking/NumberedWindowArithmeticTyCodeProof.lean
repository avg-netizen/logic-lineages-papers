module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAtomCodeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticCodecLaws

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticTyCodeProof
open NumberedWindowArithmeticPair (pair decode)
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticAtomCodeTargets
open NumberedWindowArithmeticCodecLaws

private theorem zeroRead (fuel : Nat) (σ : Ty) (h : decodeTyFuel fuel 0 = some σ) :
    encodeTy σ = 0 := by
  have e : Ty.ground = σ :=
    Option.some.inj (by cases fuel <;> simpa [decodeTyFuel] using h)
  subst σ
  rfl

theorem sound (fuel code : Nat) (σ : Ty) (h : decodeTyFuel fuel code = some σ) :
    encodeTy σ = code := by
  induction fuel generalizing code σ with
  | zero =>
    cases code with
    | zero => exact zeroRead 0 σ h
    | succ code => simp [decodeTyFuel] at h
  | succ fuel ih =>
    cases code with
    | zero => exact zeroRead (fuel+1) σ h
    | succ code =>
      cases hp : decode code with
      | none => simp [decodeTyFuel,hp] at h
      | some pr =>
        obtain ⟨a,b⟩ := pr
        cases ha : decodeTyFuel fuel a with
        | none => simp [decodeTyFuel,hp,ha] at h
        | some A =>
          cases hb : decodeTyFuel fuel b with
          | none => simp [decodeTyFuel,hp,ha,hb] at h
          | some B =>
            have e : Ty.arrow A B = σ :=
              Option.some.inj (by simpa [decodeTyFuel,hp,ha,hb] using h)
            subst σ
            simp only [encodeTy,ih a A ha,ih b B hb,pairRead hp]

theorem complete (fuel : Nat) (σ : Ty) (h : encodeTy σ ≤ fuel) :
    decodeTyFuel fuel (encodeTy σ) = some σ := by
  induction σ generalizing fuel with
  | ground => cases fuel <;> rfl
  | arrow σ τ is it =>
    cases fuel with
    | zero => simp [encodeTy] at h
    | succ f =>
      have hr : pair (encodeTy σ) (encodeTy τ) ≤ f := Nat.le_of_succ_le_succ h
      have hb := pairBounds (encodeTy σ) (encodeTy τ)
      have hs := is f (Nat.le_trans hb.1 hr)
      have ht := it f (Nat.le_trans hb.2 hr)
      simp [encodeTy,decodeTyFuel,pairRound,hs,ht]

theorem calibration : TyFuelCalibration := ⟨sound,complete⟩

theorem roundtrip (σ : Ty) : decodeTy (encodeTy σ) = some σ :=
  complete (encodeTy σ) σ (Nat.le_refl _)

theorem decodeSound {n : Nat} {σ : Ty} (h : decodeTy n = some σ) :
    encodeTy σ = n := sound n n σ h

theorem exactCodec : ExactTyCodec :=
  codec encodeTy decodeTy (fun _ _ h => decodeSound h) roundtrip

end LogicLineages.PersistentMarking.NumberedWindowArithmeticTyCodeProof
