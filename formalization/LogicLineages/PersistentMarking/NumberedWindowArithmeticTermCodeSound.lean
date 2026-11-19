import LogicLineages.PersistentMarking.NumberedWindowArithmeticAssembleSound
import LogicLineages.PersistentMarking.NumberedWindowArithmeticNodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeSound
open NumberedWindowSyntax
open NumberedWindowArithmeticPair (pair decode)
open NumberedWindowArithmeticFields NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticCodecLaws NumberedWindowArithmeticNodeProof

private theorem argsZero (fuel : Nat) (qs : NArgs) (h : decodeArgsFuel fuel 0 = some qs) :
    encodeArgs qs = 0 := by
  have e : NArgs.nil = qs :=
    Option.some.inj (by cases fuel <;> simpa [decodeArgsFuel] using h)
  subst qs
  rfl

theorem atFuel (fuel : Nat) :
    (∀ code Q, decodeTermFuel fuel code = some Q → encodeTerm Q = code) ∧
    (∀ code qs, decodeArgsFuel fuel code = some qs → encodeArgs qs = code) := by
  induction fuel with
  | zero =>
    constructor
    · intro c Q h; cases h
    · intro c qs h
      cases c with
      | zero => exact argsZero 0 qs h
      | succ c => simp [decodeArgsFuel] at h
  | succ fuel ih =>
    obtain ⟨tSound,aSound⟩ := ih
    constructor
    · intro code Q h
      have hh : (decodeNode code).bind (fun p =>
          assemble (decodeTermFuel fuel) (decodeArgsFuel fuel) p.1 p.2) = some Q := h
      obtain ⟨p,hp,ha⟩ := Option.bind_eq_some_iff.mp hh
      obtain ⟨tag,fields⟩ := p
      exact (NumberedWindowArithmeticAssembleSound.sound
        (decodeTermFuel fuel) (decodeArgsFuel fuel) tSound aSound tag fields Q ha).trans (nodeRead hp)
    · intro code qs h
      cases code with
      | zero => exact argsZero (fuel+1) qs h
      | succ code =>
        cases hp : decode code with
        | none => simp [decodeArgsFuel,hp] at h
        | some pr =>
          obtain ⟨a,b⟩ := pr
          cases ha : decodeTermFuel fuel a with
          | none => simp [decodeArgsFuel,hp,ha] at h
          | some Q =>
            cases hb : decodeArgsFuel fuel b with
            | none => simp [decodeArgsFuel,hp,ha,hb] at h
            | some bs =>
              have e : NArgs.cons Q bs = qs :=
                Option.some.inj (by simpa [decodeArgsFuel,hp,ha,hb] using h)
              subst qs
              simp only [encodeArgs,tSound a Q ha,aSound b bs hb,pairRead hp]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeSound
