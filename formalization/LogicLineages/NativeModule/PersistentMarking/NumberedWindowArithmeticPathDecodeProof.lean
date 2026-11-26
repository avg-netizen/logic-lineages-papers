module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPathCheckTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPathCodeChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathDecodeProof
open NumberedWindowSyntax NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticPathCheckTargets
open NumberedWindowArithmeticRawHopCodeProof
universe u

theorem termAt {Q : NTerm} {code : Nat} (h : encodeTerm Q = code) :
    decodeTerm code = some Q := by
  rw [← h]
  exact NumberedWindowArithmeticTermCodeComplete.termRound Q

theorem betweenTrue {α : Type u} (read : Nat → Option α) (test : NTerm → α → NTerm → Bool)
    (src cert dst : Nat) :
    (between read test src cert dst = true ↔
      ∃ Q w R, decodeTerm src = some Q ∧ read cert = some w ∧ decodeTerm dst = some R ∧
        test Q w R = true) := by
  constructor
  · intro h
    cases hQ : decodeTerm src <;> cases hw : read cert <;> cases hR : decodeTerm dst <;>
      simp only [between,hQ,hw,hR,Bool.false_eq_true] at h
    exact ⟨_,_,_,rfl,rfl,rfl,h⟩
  · rintro ⟨Q,w,R,hQ,hw,hR,h⟩
    simpa only [between,hQ,hw,hR] using h

theorem betweenExists {α : Type u} (enc : α → Nat) (read : Nat → Option α)
    (round : ∀ w, read (enc w) = some w)
    (test : NTerm → α → NTerm → Bool) (actual : NTerm → NTerm → Prop)
    (exactly : ∀ Q R, (∃ w, test Q w R = true) ↔ actual Q R)
    (src dst : Nat) :
    ((∃ c, between read test src c dst = true) ↔
      ∃ Q R, encodeTerm Q = src ∧ encodeTerm R = dst ∧ actual Q R) := by
  constructor
  · rintro ⟨c,h⟩
    obtain ⟨Q,w,R,hQ,_,hR,ht⟩ := (betweenTrue read test src c dst).mp h
    exact ⟨Q,R,termRead hQ,termRead hR,(exactly Q R).mp ⟨w,ht⟩⟩
  · rintro ⟨Q,R,hQ,hR,h⟩
    obtain ⟨w,ht⟩ := (exactly Q R).mpr h
    exact ⟨enc w,(betweenTrue read test src (enc w) dst).mpr
      ⟨Q,w,R,termAt hQ,round w,termAt hR,ht⟩⟩

theorem betweenMalformed {α : Type u} (read : Nat → Option α)
    (test : NTerm → α → NTerm → Bool) (src cert dst : Nat)
    (h : MissingPayload read src cert dst) : between read test src cert dst = false := by
  rcases h with h | h | h
  · cases hw : read cert <;> cases hR : decodeTerm dst <;> simp [between,h,hw,hR]
  · cases hQ : decodeTerm src <;> cases hR : decodeTerm dst <;> simp [between,hQ,h,hR]
  · cases hQ : decodeTerm src <;> cases hw : read cert <;> simp [between,hQ,hw,h]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathDecodeProof
