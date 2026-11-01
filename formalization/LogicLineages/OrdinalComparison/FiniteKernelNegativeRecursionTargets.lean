module
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- This is a numerical counterexample to extending the printed signed
recurrence by clamping nonpositive iteration depths to zero. It does not
say that an undefined source expression has a value. -/
def ActualNegativeFiniteKernelRecursionCounterexample : Prop :=
  ∀ c t : Nat, c+7 ≤ t →
    let entry := actualSuffixKernel (Ordinal.omega0 ^ (2 : Ordinal)) (c+2) t
    0 < signedKernelDepth 2 c (-2) t ∧
    signedKernelDepth 1 c (-2) entry = -1 ∧
    rawSignedKernelValue 2 c (-2) t < rawSignedKernelValue 1 c (-2) entry

end LogicLineages.OrdinalComparison.Targets
