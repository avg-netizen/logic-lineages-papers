module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.SuccessorSmallTargets
open OrdinalComparison

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

def ActualPhiEven : Prop := ∀ t : Nat, Even (Phi t)

def ActualOmegaSuffixKernel : Prop :=
  ∀ a t : Nat, a + 2 ≤ t →
    actualSuffixKernelCount Ordinal.omega0 a t = 1 ∧
      actualSuffixKernel Ordinal.omega0 a t = Phi t

def ActualOmegaSquaredSuffixCount : Prop :=
  ∀ a t : Nat, a + 3 ≤ t →
    actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) a t =
      Phi t / 2 - (a + 1) / 2 + 1

def ActualOmegaSquaredMassClasses : Prop :=
  ∀ a b t : Nat, a + 3 ≤ t → b + 3 ≤ t →
    (actualSuffixKernel (Ordinal.omega0 ^ (2 : Ordinal)) a t =
      actualSuffixKernel (Ordinal.omega0 ^ (2 : Ordinal)) b t ↔
        (a + 1) / 2 = (b + 1) / 2) ∧
    (actualSuffixKernel (Ordinal.omega0 ^ (2 : Ordinal)) a t <
      actualSuffixKernel (Ordinal.omega0 ^ (2 : Ordinal)) b t ↔
        (b + 1) / 2 < (a + 1) / 2)

def FullActualSmallPrincipalKernels : Prop :=
  ActualPhiEven ∧ ActualOmegaSuffixKernel ∧ ActualOmegaSquaredSuffixCount ∧
    ActualOmegaSquaredMassClasses

end LogicLineages.StandardControlCurrent.SuccessorSmallTargets
