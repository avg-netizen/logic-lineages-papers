module
public import LogicLineages.OrdinalComparison.LimitMassFirstDefinitions
public import LogicLineages.OrdinalComparison.AdjacentPackedDefinitions
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Entire paper07 thm:limitmass599–655: (6.6) plus its effective genuine-tail
lexicographic consequence and equal-pair agreement. Thresholds depend on the
fixed literal profile, never uniformly on all profiles at once. -/
def ActualLimitMassProfileSeparation : Prop :=
  ∀ L : NONote, ∀ beta : Ordinal.{0}, Order.IsSuccLimit beta →
    L.1.repr = Ordinal.omega0^beta → ∀ E : FixedLimitPositiveExpr,
    fixedLimitProfileBelow L.1.repr E → ∀ t c e : Nat,
    profileLimitMassThreshold L E ≤ t → c < e → e+actualOrdinalNorm L.1.repr ≤ t →
      actualFixedLimitProfileEval E (actualSuffixKernel L.1.repr e t + actualSuffixKernelCount L.1.repr e t) <
        actualSuffixKernel L.1.repr c t

def ActualLimitLexicographicSeparation : Prop :=
  ∀ L : NONote, ∀ beta : Ordinal.{0}, Order.IsSuccLimit beta →
    L.1.repr = Ordinal.omega0^beta → ∀ E : FixedLimitPositiveExpr,
    fixedLimitProfileBelow L.1.repr E → ∀ t u c e : Nat,
    max (profileLimitMassThreshold L E) (profileAdjacentThreshold L E) ≤ t →
    c+actualOrdinalNorm L.1.repr ≤ u → e+actualOrdinalNorm L.1.repr ≤ t →
      ((t < u ∨ (t=u ∧ c<e)) →
        actualFixedLimitProfileEval E (actualSuffixKernel L.1.repr e t + actualSuffixKernelCount L.1.repr e t) <
          actualSuffixKernel L.1.repr c u) ∧
      ((t=u ∧ c=e) → actualSuffixKernel L.1.repr c u = actualSuffixKernel L.1.repr e t)

def FullActualLimitExponentMassSeparation : Prop :=
  ActualLimitMassProfileSeparation ∧ ActualLimitLexicographicSeparation

end LogicLineages.OrdinalComparison.Targets
