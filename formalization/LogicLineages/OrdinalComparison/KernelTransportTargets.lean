module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual transport suppliers for paper07 lem:direct (499–519).
The same-control comparison uses explicit numerical monotone/expansive control,
never an assumed endpoint or kernel ordering law. -/
def ActualControlledExitNormMonotone : Prop :=
  ∀ g : Nat → Nat, Monotone g → (∀ n : Nat, n ≤ g n) →
    ∀ A B : Ordinal.{0}, A ≤ B → B < epsilonZero → actualOrdinalNorm A ≤ actualOrdinalNorm B →
      actualOrdinalNorm (actualControlledStateAfter g A (actualControlledCount g A)) ≤
        actualOrdinalNorm (actualControlledStateAfter g B (actualControlledCount g B))

def ActualSuffixKernelFirstMaximum : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ c t : Nat, c + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t →
      let pi := Ordinal.omega0 ^ beta
      let Q := actualMaximumPredecessor pi (Phi t - c)
      let g := compensatedPrefixControl c
      actualControlledStateAfter g (actualSuffixKernelInitial pi c t) 1 = Q ∧
      actualSuffixKernelCount pi c t = actualControlledCount g Q + 1 ∧
      actualSuffixKernel pi c t = c + actualOrdinalNorm
        (actualControlledStateAfter g Q (actualControlledCount g Q))

def ActualSuffixKernelBelowFixedHead : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ c t : Nat, c + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t →
      actualSuffixKernel (Ordinal.omega0 ^ beta) c t ≤
        actualCollapse (Ordinal.omega0 ^ beta + (t : Ordinal))

end LogicLineages.OrdinalComparison.Targets
