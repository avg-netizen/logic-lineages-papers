module
public import LogicLineages.OrdinalComparison.RangeRangeNodeTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Entire ORIGINAL RR equal-outer local rule including the requested
bare-limit quantitative gap, using the actual common numeric RR programme.
This is one case of the still pending full original RR local theorem. -/
def ActualSameOuterRangeQueryNodeCorrect : Prop :=
  ∀ (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat) (E F : FixedLimitPositiveExpr),
    oneVariableComparisonValid (.range (w++[(eta,c)]) E) →
    oneVariableComparisonValid (.range (v++[(eta,d)]) F) →
  ∀ (leftProfile rightProfile : Nat) (table : ComparisonNodeTable),
    let q : ComparisonQuery := ((oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (.range (v++[(eta,d)]) F)),(leftProfile,rightProfile))
    comparisonQueryTableCovers q table → actualComparisonQueryCorrect q (encodedRangeRangeQueryNode q table)

end LogicLineages.OrdinalComparison.Targets
