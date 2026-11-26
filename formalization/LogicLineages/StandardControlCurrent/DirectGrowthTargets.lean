module
public import LogicLineages.OrdinalComparison.ProfileDominatorDefinitions
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.DirectGrowthTargets
open OrdinalComparison

def ActualUniformProfileDirectGrowth : Prop :=
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell) →
    Ordinal.omega0 < L.1.repr → ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr E →
    ∀ t c : Nat, profileDirectThreshold L E ≤ t → c + actualOrdinalNorm L.1.repr ≤ t →
      actualFixedLimitProfileEval E t < actualSuffixKernel L.1.repr c t

def ActualSuffixKernelBelowFixedHead : Prop :=
  ∀ beta : Ordinal.{0}, 0 < beta → Ordinal.omega0 ^ beta < epsilonZero →
    ∀ c t : Nat, c + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t →
      actualSuffixKernel (Ordinal.omega0 ^ beta) c t ≤
        actualCollapse (Ordinal.omega0 ^ beta + (t : Ordinal))


def Full : Prop := ActualUniformProfileDirectGrowth ∧ ActualSuffixKernelBelowFixedHead
end LogicLineages.StandardControlCurrent.DirectGrowthTargets
