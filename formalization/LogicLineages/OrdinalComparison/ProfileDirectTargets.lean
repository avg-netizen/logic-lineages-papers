module
public import LogicLineages.OrdinalComparison.ProfileDirectPackedTargets
public import LogicLineages.OrdinalComparison.KernelTransportTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Full paper07 lem:direct (499–519), with explicit executable threshold on
faithful finite syntax and every genuine retained mass, plus the head bound. -/
def ActualUniformProfileDirectGrowth : Prop :=
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell) →
    Ordinal.omega0 < L.1.repr → ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr E →
    ∀ t c : Nat, profileDirectThreshold L E ≤ t → c + actualOrdinalNorm L.1.repr ≤ t →
      actualFixedLimitProfileEval E t < actualSuffixKernel L.1.repr c t

def FullActualDirectKernelGrowth : Prop :=
  ActualUniformProfileDirectGrowth ∧ ActualSuffixKernelBelowFixedHead

end LogicLineages.OrdinalComparison.Targets
