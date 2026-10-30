module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Entire paper07 lem:small (paper.tex684–699), including genuine numerical
input domains and its exact same-input reverse mass classes. Ceil(a/2) is
represented by (a+1)/2 in Nat; no truncation side condition is borrowed. -/
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

end LogicLineages.OrdinalComparison.Targets
