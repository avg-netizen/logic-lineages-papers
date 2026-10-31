module
public import LogicLineages.OrdinalComparison.ControlDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

/-- Numeric majorant for one genuine exponential/product box step. -/
def OriginalBoxNumericalStep : Prop :=
  ∀ x s : Nat, s ≤ x → 2 ^ x * s ≤ 2 ^ (2 ^ x)

/-- Exact F2 envelope used in original Lemma 2.11, rather than a larger
control function or a changed collapse side condition. -/
def OriginalBoxControlEnvelope : Prop :=
  ∀ s n : Nat, 0 < s →
    (fastControl 0)^[2 * n] (s + 1) ≤ fastControl 2 (s + n)

end LogicLineages.OrdinalComparison.Source.Targets
