module
public import LogicLineages.OrdinalComparison.BinaryPoleRemovalDefinitions
public import LogicLineages.OrdinalComparison.LinkedResidueDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual observation lies beyond the source higher-pole transient.
The proved route μ≤d² supplies a≤B; it is not claimed to be the source's
separate printed estimate μ≤d(1+floor(log2 d)). No growth premise is assumed. -/
def ActualBinaryPoleBudgetQuadratic : Prop :=
  ∀ d : Nat, actualBinaryPoleBudget d ≤ d ^ 2

def ActualLinkedPoleTransient : Prop :=
  ∀ u : Nat, 5 ≤ u →
    actualBinaryPoleTransient (actualLinkedCutoff u) ≤ actualLinkedBudget u ∧
    actualLinkedBudget u + 1 ≤ actualLinkedBinaryExponent (u + 1) ∧
    Phi (u + 1) = 2 ^ actualLinkedBinaryExponent (u + 1)

end LogicLineages.OrdinalComparison.Targets
