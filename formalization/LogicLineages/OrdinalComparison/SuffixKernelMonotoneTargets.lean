module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lines403–408: genuine input/mass monotonicity of literal kernels.
These are numerical semantic conclusions, not an effectiveness certificate. -/
def ActualSuffixCountInputMassMonotone : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ a b t u : Nat, a ≤ b → t ≤ u →
      b + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t →
      a + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ u →
      actualSuffixKernelCount (Ordinal.omega0 ^ beta) b t ≤
        actualSuffixKernelCount (Ordinal.omega0 ^ beta) a u

def ActualSuffixKernelInputMassMonotone : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ a b t u : Nat, a ≤ b → t ≤ u →
      b + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t →
      a + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ u →
      actualSuffixKernel (Ordinal.omega0 ^ beta) b t ≤
        actualSuffixKernel (Ordinal.omega0 ^ beta) a u

def ActualSuffixKernelStrictInput : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ a b t u : Nat, a ≤ b → t < u →
      b + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t →
      a + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ u →
      actualSuffixKernel (Ordinal.omega0 ^ beta) b t <
        actualSuffixKernel (Ordinal.omega0 ^ beta) a u

end LogicLineages.OrdinalComparison.Targets
