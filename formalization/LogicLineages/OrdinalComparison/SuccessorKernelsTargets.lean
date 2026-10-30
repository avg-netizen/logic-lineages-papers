module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Full paper07 lem:successor (658–682), exact source common genuine domain.
All counts and kernels are the literal ordinal controlled descent definitions. -/
def ActualSuccessorCountCocycle : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma →
    Ordinal.omega0 ^ gamma * Ordinal.omega0 < epsilonZero → ∀ c t : Nat,
      let theta := Ordinal.omega0 ^ gamma
      let L := theta * Ordinal.omega0
      let w := actualOrdinalNorm theta
      c + w + actualOrdinalNorm L ≤ t →
        actualSuffixKernelCount L c t = actualSuffixKernelCount L (c + w) t +
          actualSuffixKernelCount theta c (actualSuffixKernel L (c + w) t)

def ActualSuccessorKernelComposition : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma →
    Ordinal.omega0 ^ gamma * Ordinal.omega0 < epsilonZero → ∀ c t : Nat,
      let theta := Ordinal.omega0 ^ gamma
      let L := theta * Ordinal.omega0
      let w := actualOrdinalNorm theta
      c + w + actualOrdinalNorm L ≤ t →
        actualSuffixKernel L c t =
          actualSuffixKernel theta c (actualSuffixKernel L (c + w) t)

def FullActualSuccessorCutCocycle : Prop :=
  ActualSuccessorCountCocycle ∧ ActualSuccessorKernelComposition

end LogicLineages.OrdinalComparison.Targets
