module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeCases

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeComplete
open NumberedWindowSyntax NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticTermCodeCases

theorem atFuel (fuel : Nat) : GoodTerm fuel ∧ GoodArgs fuel := by
  induction fuel with
  | zero =>
    constructor
    · intro Q h
      have hp := termPositive Q
      omega
    · intro qs h
      cases qs with
      | nil => rfl
      | cons Q qs => simp [encodeArgs] at h
  | succ fuel ih =>
    exact ⟨termStep fuel ih.1 ih.2,argsStep fuel ih.1 ih.2⟩

theorem termRound (Q : NTerm) : decodeTerm (encodeTerm Q) = some Q :=
  (atFuel (encodeTerm Q)).1 Q (Nat.le_refl _)

theorem argsRound (qs : NArgs) : decodeArgs (encodeArgs qs) = some qs :=
  (atFuel (encodeArgs qs)).2 qs (Nat.le_refl _)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeComplete
