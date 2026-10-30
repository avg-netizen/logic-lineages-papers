module
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Numerical reserve gap in paper07 adjacent proof 568–580. Phi is literal;
all exponential/iterate growth is proved, not an extra premise. The later cut
supplies actual counts D and q and actual retained mass p. -/
def ActualAdjacentNumericalGap : Prop :=
  ∀ R t D q p : Nat, R+5 ≤ t → 0 < D → D ≤ q+1 →
    p ≤ (R+1) * (Phi^[D]) t →
      let Z := (Phi^[D]) t
      Z+D < (Phi^[q]) (Phi (t+1)) - p

end LogicLineages.OrdinalComparison.Targets
