module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPairChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticPair (pair decode)
universe u

theorem pairBounds (a b : Nat) : a ≤ pair a b ∧ b ≤ pair a b :=
  NumberedWindowArithmeticPairChecks.exact_PairComponentBounds a b

theorem pairRead {n a b : Nat} (h : decode n = some (a,b)) : pair a b = n :=
  (NumberedWindowArithmeticPairChecks.exact_PairDecode n a b).mp h

theorem pairRound (a b : Nat) : decode (pair a b) = some (a,b) :=
  NumberedWindowArithmeticPairChecks.exact_PairRoundtrip a b

theorem codec {α : Type u} (enc : α → Nat) (dec : Nat → Option α)
    (sound : ∀ n a, dec n = some a → enc a = n)
    (roundtrip : ∀ a, dec (enc a) = some a) :
    (∀ n a, dec n = some a ↔ enc a = n) ∧
    (∀ a, dec (enc a) = some a) ∧
    (∀ n, dec n = none ↔ ¬ ∃ a, enc a = n) := by
  refine ⟨?_,roundtrip,?_⟩
  · intro n a
    exact ⟨sound n a,fun h => h ▸ roundtrip a⟩
  · intro n
    constructor
    · intro hn h
      obtain ⟨a,he⟩ := h
      have hs := roundtrip a
      rw [he,hn] at hs
      cases hs
    · intro h
      cases he : dec n with
      | none => rfl
      | some a => exact False.elim (h ⟨a,sound n a he⟩)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticCodecLaws
