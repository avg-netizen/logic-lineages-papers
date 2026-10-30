module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 paper.tex339–355: literal retained-mass suffix semantics. Numerical
mass need not be the norm of an ordinal prefix. No encoded computability claim. -/
def ActualSuffixKernelInput : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ a t : Nat, a + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t →
      actualSuffixKernelInitial (Ordinal.omega0 ^ beta) a t < epsilonZero ∧
      Ordinal.omega0 ≤ actualSuffixKernelInitial (Ordinal.omega0 ^ beta) a t ∧
      a + actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ beta) a t) = t

def ActualSuffixKernelTrace : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ a t : Nat, a + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t →
      let pi := Ordinal.omega0 ^ beta
      let I := actualSuffixKernelInitial pi a t
      let E := actualSuffixKernelCount pi a t
      let state := actualControlledStateAfter (compensatedPrefixControl a) I
      0 < E ∧
      (∀ i : Nat, i ≤ E → a + actualOrdinalNorm (state i) = (Phi^[i]) t) ∧
      state E < Ordinal.omega0 ∧
      (∀ i : Nat, i < E → Ordinal.omega0 ≤ state i) ∧
      actualOrdinalNorm (state E) = actualSuffixKernel pi a t - a ∧
      actualSuffixKernel pi a t ∈ Set.range Phi

end LogicLineages.OrdinalComparison.Targets
