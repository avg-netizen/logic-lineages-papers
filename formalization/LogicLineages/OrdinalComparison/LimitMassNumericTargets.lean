module
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual control growth and the numerical reserve gap in paper07 limitmass
637–644. No exponential/profile growth is supplied as a premise. -/
def ActualPhiSquareGap : Prop := ∀ n : Nat, n*n < Phi n

def ActualLimitMassNumericalGap : Prop :=
  ∀ R t D q p : Nat, R+4 ≤ t → 0 < D → D ≤ q+1 →
    p ≤ (R+1)*(Phi^[D]) t →
      let Z := (Phi^[D]) t
      Z+D < (Phi^[q]) (Phi (Phi t)) - p

end LogicLineages.OrdinalComparison.Targets
