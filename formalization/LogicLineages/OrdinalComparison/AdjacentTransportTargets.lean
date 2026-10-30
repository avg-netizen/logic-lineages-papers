module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual endpoint and worst-retained-mass transport for paper07 adjacent.
Arbitrary controls in the first target refer to their own states, not the
special Phi terminal-value function. -/
def ActualControlledEndpointAlongTrace : Prop :=
  ∀ g : Nat → Nat, ∀ A : Ordinal.{0}, A < epsilonZero → ∀ i : Nat,
    i ≤ actualControlledCount g A →
      actualControlledStateAfter g (actualControlledStateAfter g A i)
        (actualControlledCount g (actualControlledStateAfter g A i)) =
      actualControlledStateAfter g A (actualControlledCount g A)

def ActualWorstMassKernelMonotone : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ t u : Nat, actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t → t ≤ u →
      actualSuffixKernel (Ordinal.omega0 ^ beta) (t-actualOrdinalNorm (Ordinal.omega0 ^ beta)) t ≤
        actualSuffixKernel (Ordinal.omega0 ^ beta) (u-actualOrdinalNorm (Ordinal.omega0 ^ beta)) u

end LogicLineages.OrdinalComparison.Targets
