module
public import LogicLineages.PermittedControl.RelativeDescentDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Supporting induction consequence immediately following lem:propagation.
Budgets remain explicit hypotheses here; gap-input must separately derive them.
No survival or count inequality is assumed, including at initial upper lag k. -/
def CountLag : Prop := ∀ (f g : Nat → Nat) (B C : Nat),
  SelectedWithThreshold f B → SelectedWithThreshold g C →
  ∀ (lam mu lam' mu' : Ordinal.{0}) (t u tau sigma k S : Nat),
  lam < epsilonZero → lam' < epsilonZero →
  Order.IsSuccLimit lam → Order.IsSuccLimit lam' →
  (mu = 0 ∨ Order.IsSuccLimit mu) → (mu' = 0 ∨ Order.IsSuccLimit mu') →
  mu < lam → mu' < lam' →
  max 2 (max (actualOrdinalNorm lam) (actualOrdinalNorm mu)) ≤ t →
  max 2 (max (actualOrdinalNorm lam') (actualOrdinalNorm mu')) ≤ u →
  actualOrdinalNorm mu ≤ S → actualOrdinalNorm mu' ≤ S →
  FirstEntry f (countInitial lam t) mu tau →
  FirstEntry g (countInitial lam' u) mu' sigma →
  ((actualLimitPart (relativeState f lam mu t 0) <
      actualLimitPart (relativeState g lam' mu' u k)) →
    (∀ i : Nat, i < tau → f^[i] t + S ≤ g^[i+k+1] u) → tau+k < sigma) ∧
  ((actualLimitPart (relativeState f lam mu t 0) ≤
      actualLimitPart (relativeState g lam' mu' u k)) →
    (∀ i : Nat, i < tau → f^[i+1] t + S ≤ g^[i+k+1] u) → tau+k ≤ sigma)

end LogicLineages.PermittedControl.Targets
