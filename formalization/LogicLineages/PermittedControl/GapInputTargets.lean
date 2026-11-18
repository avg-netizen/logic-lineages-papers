module
public import LogicLineages.PermittedControl.GapInputDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Genuine computed finite-code tail, with literal actual-ordinal norm bridge. -/
def GapInputTailEffective : Prop := Computable encodedGapInputTail ∧
  ∀ (lam mu lam' mu' : NONote) (k : Nat),
    encodedGapInputTail (rawNoteEncode lam.1, rawNoteEncode mu.1,
      rawNoteEncode lam'.1, rawNoteEncode mu'.1, k) =
      gapInputTail lam.1.repr mu.1.repr lam'.1.repr mu'.1.repr k

/-- Full source lem:gap-input at an explicit effective tail. Each conclusion
includes actual first-entry existence and strict terminal norm comparison.
No relative residue, survival, budget-margin or reserve-norm oracle premise. -/
def GapInputComparison : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lam mu lam' mu' : Ordinal.{0}), lam < epsilonZero → lam' < epsilonZero →
    Order.IsSuccLimit lam → Order.IsSuccLimit lam' →
    (mu = 0 ∨ Order.IsSuccLimit mu) → (mu' = 0 ∨ Order.IsSuccLimit mu') →
    mu < lam → mu' < lam' →
    ((lam'-mu' < lam-mu) → ∀ t : Nat, gapInputTail lam mu lam' mu' 0 ≤ t →
      ∃ i j : Nat, FirstEntry f (countInitial lam t) mu i ∧
        FirstEntry f (countInitial lam' t) mu' j ∧ j < i ∧
        entryNormAt f (countInitial lam' t) j < entryNormAt f (countInitial lam t) i) ∧
    ((lam'-mu' ≤ lam-mu) → ∀ t u : Nat,
      gapInputTail lam mu lam' mu' 0 ≤ t → gapInputTail lam mu lam' mu' 0 ≤ u → u < t →
      ∃ i j : Nat, FirstEntry f (countInitial lam t) mu i ∧
        FirstEntry f (countInitial lam' u) mu' j ∧ j ≤ i ∧
        entryNormAt f (countInitial lam' u) j < entryNormAt f (countInitial lam t) i) ∧
    (∀ k : Nat, 0 < k → lam'-mu' + Ordinal.omega0*(k : Ordinal) ≤ lam-mu →
      ∀ t u : Nat, gapInputTail lam mu lam' mu' k ≤ t → gapInputTail lam mu lam' mu' k ≤ u →
      u + gapProfileBound mu mu' ≤ f^[k] t →
      ∃ i j : Nat, FirstEntry f (countInitial lam t) mu i ∧
        FirstEntry f (countInitial lam' u) mu' j ∧ j+k ≤ i ∧
        entryNormAt f (countInitial lam' u) j < entryNormAt f (countInitial lam t) i)

end LogicLineages.PermittedControl.Targets
