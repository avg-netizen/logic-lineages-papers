module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticCodecLaws

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldsProof
open NumberedWindowArithmeticPair (pair decode)
open NumberedWindowArithmeticFields NumberedWindowArithmeticTermCodeTargets
open NumberedWindowArithmeticCodecLaws

private theorem zeroRead (fuel : Nat) (xs : List Nat) (h : decodeFieldsFuel fuel 0 = some xs) :
    encodeFields xs = 0 := by
  have e : ([] : List Nat) = xs :=
    Option.some.inj (by cases fuel <;> simpa [decodeFieldsFuel] using h)
  subst xs
  rfl

theorem sound (fuel code : Nat) (xs : List Nat) (h : decodeFieldsFuel fuel code = some xs) :
    encodeFields xs = code := by
  induction fuel generalizing code xs with
  | zero =>
    cases code with
    | zero => exact zeroRead 0 xs h
    | succ code => simp [decodeFieldsFuel] at h
  | succ fuel ih =>
    cases code with
    | zero => exact zeroRead (fuel+1) xs h
    | succ code =>
      cases hp : decode code with
      | none => simp [decodeFieldsFuel,hp] at h
      | some pr =>
        obtain ⟨a,b⟩ := pr
        cases hb : decodeFieldsFuel fuel b with
        | none => simp [decodeFieldsFuel,hp,hb] at h
        | some bs =>
          have e : a :: bs = xs :=
            Option.some.inj (by simpa [decodeFieldsFuel,hp,hb] using h)
          subst xs
          simp only [encodeFields,ih b bs hb,pairRead hp]

theorem complete (fuel : Nat) (xs : List Nat) (h : encodeFields xs ≤ fuel) :
    decodeFieldsFuel fuel (encodeFields xs) = some xs := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons a xs ih =>
    cases fuel with
    | zero => simp [encodeFields] at h
    | succ f =>
      have hr : pair a (encodeFields xs) ≤ f := Nat.le_of_succ_le_succ h
      have hb := (pairBounds a (encodeFields xs)).2
      have ht := ih f (Nat.le_trans hb hr)
      simp [encodeFields,decodeFieldsFuel,pairRound,ht]

theorem calibration : FieldsFuelCalibration := ⟨sound,complete⟩

theorem fieldsRound (xs : List Nat) : decodeFields (encodeFields xs) = some xs :=
  complete (encodeFields xs) xs (Nat.le_refl _)

theorem fieldsRead {n : Nat} {xs : List Nat} (h : decodeFields n = some xs) :
    encodeFields xs = n := sound n n xs h

theorem exactCodec : ExactFieldsCodec :=
  codec encodeFields decodeFields (fun _ _ h => fieldsRead h) fieldsRound

end LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldsProof
