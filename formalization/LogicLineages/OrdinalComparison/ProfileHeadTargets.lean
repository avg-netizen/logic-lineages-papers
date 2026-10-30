module
public import LogicLineages.OrdinalComparison.ProfileHeadDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:reserve (464–495), actual head facts needed by its compiler.
Every natural argument is retained, including zero; no head law is a premise. -/
def ActualFixedLimitProfileHeads : Prop :=
  ∀ rho : NONote, Order.IsSuccLimit rho.1.repr →
    StrictMono (actualProfileHead rho) ∧ ∀ n : Nat, n < actualProfileHead rho n

def ActualOmegaProfileHead : Prop :=
  profileOmegaNote.1.repr = Ordinal.omega0 ∧
    ∀ n : Nat, 2 * n < actualProfileHead profileOmegaNote n

end LogicLineages.OrdinalComparison.Targets
