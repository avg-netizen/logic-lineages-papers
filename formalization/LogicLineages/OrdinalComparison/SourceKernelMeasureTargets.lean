module
public import LogicLineages.OrdinalComparison.SourceKernelMeasureDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def SourceKernelHistogramPermutation : Prop :=
  ∀ (budget : Nat) (u v : List NONote), u.Perm v →
    comparisonKernelHistogram (encodedNormalNormBall budget).length (comparisonSourceKernelRanks budget u)=
      comparisonKernelHistogram (encodedNormalNormBall budget).length (comparisonSourceKernelRanks budget v)

/-- Actual ordinal-valued occurrence/rank termination supplier: no arbitrary
rank/decrease/ordering interface is a premise. Norm-ball ranking and strict
actual ordinal order are linked by proved suppliers. Full source child-call
membership and the complete two-sort comparison remain separate obligations. -/
def SourceKernelStepWellFounded : Prop := ∀ budget : Nat, WellFounded (ComparisonSourceKernelStep budget)

end LogicLineages.OrdinalComparison.Targets
