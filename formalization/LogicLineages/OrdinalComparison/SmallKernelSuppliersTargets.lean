module
public import LogicLineages.OrdinalComparison.ControlledCountDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Literal source suppliers for paper07 lem:small, paper.tex684–699.
The numerical b≥2 condition is explicit and must be derived at the source use. -/
def ActualOmegaMaximum : Prop :=
  ∀ b : Nat, actualMaximumPredecessor Ordinal.omega0 b = (b : Ordinal)

def ActualOmegaSquaredMaximum : Prop :=
  ∀ b : Nat, 2 ≤ b →
    actualMaximumPredecessor (Ordinal.omega0 ^ (2 : Ordinal)) b =
      Ordinal.omega0 * ((b / 2 : Nat) : Ordinal) + ((b % 2 : Nat) : Ordinal)

def ActualExpansiveControlLinearCount : Prop :=
  ∀ g : Nat → Nat, (∀ n : Nat, n ≤ g n) → ∀ k n : Nat,
    actualControlledCount g (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) = k

end LogicLineages.OrdinalComparison.Targets
