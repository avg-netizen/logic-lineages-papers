module
public import LogicLineages.OrdinalComparison.ComparisonMeasureDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- A genuine finite replacement theorem for arbitrary higher-rank insertions,
not a supplied decrease field on a source-comparison interface. -/
def ComparisonHistogramReplacement : Prop :=
  ∀ (m : Nat) (before after added : List Nat) (r : Nat), r<m →
    (∀ s∈added,r<s) →
    ComparisonKernelHistogramLt m (comparisonKernelHistogram m (before++added++after))
      (comparisonKernelHistogram m (before++r::after))

/-- Entire mathematical weighted-multiset termination core for each finite
signature. Source-signature construction, actual call graph closure and the
full sign algorithm are explicitly NOT asserted by this supplier. -/
def ComparisonRankStepWellFounded : Prop := ∀ m : Nat, WellFounded (ComparisonRankStep m)

end LogicLineages.OrdinalComparison.Targets
