module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticWitnessListCode
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticWitnessListCodeProof
open NumberedWindowSyntax NumberedWindowArithmeticFields NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticWitnessListCode NumberedWindowArithmeticFieldsProof
universe u

private theorem elementsSound {α : Type u} (enc : α → Nat) (dec : Nat → Option α)
    (sound : ∀ n x, dec n = some x → enc x = n) (codes : List Nat) (xs : List α)
    (h : decodeElements dec codes = some xs) : xs.map enc = codes := by
  induction codes generalizing xs with
  | nil =>
    have e : ([] : List α) = xs := Option.some.inj h
    subst xs
    rfl
  | cons n ns ih =>
    simp only [decodeElements,Option.bind_eq_bind,Option.bind_eq_some_iff,
      Option.pure_def,Option.some.injEq] at h
    obtain ⟨a,ha,as',hs,rfl⟩ := h
    simp only [List.map_cons,sound _ _ ha,ih _ hs]

private theorem elementsRound {α : Type u} (enc : α → Nat) (dec : Nat → Option α)
    (round : ∀ x, dec (enc x) = some x) (xs : List α) :
    decodeElements dec (xs.map enc) = some xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [decodeElements,round,ih]

theorem decodeSound {α : Type u} (enc : α → Nat) (dec : Nat → Option α)
    (sound : ∀ n x, dec n = some x → enc x = n) (n : Nat) (xs : List α)
    (h : decodeListOf dec n = some xs) : encodeListOf enc xs = n := by
  change (decodeFields n).bind (decodeElements dec) = some xs at h
  obtain ⟨codes,hc,hs⟩ := Option.bind_eq_some_iff.mp h
  simpa only [encodeListOf,elementsSound enc dec sound _ _ hs] using fieldsRead hc

theorem decodeRound {α : Type u} (enc : α → Nat) (dec : Nat → Option α)
    (round : ∀ x, dec (enc x) = some x) (xs : List α) :
    decodeListOf dec (encodeListOf enc xs) = some xs := by
  simpa only [decodeListOf,encodeListOf,fieldsRound,Option.bind_some] using
    elementsRound enc dec round xs

theorem termsSound (n : Nat) (xs : List NTerm) (h : decodeTermList n = some xs) :
    encodeTermList xs = n :=
  decodeSound encodeTerm decodeTerm
    (fun c Q h => (NumberedWindowArithmeticTermCodeSound.atFuel c).1 c Q h) n xs h

theorem termsRound (xs : List NTerm) : decodeTermList (encodeTermList xs) = some xs :=
  decodeRound encodeTerm decodeTerm NumberedWindowArithmeticTermCodeComplete.termRound xs

end LogicLineages.PersistentMarking.NumberedWindowArithmeticWitnessListCodeProof
