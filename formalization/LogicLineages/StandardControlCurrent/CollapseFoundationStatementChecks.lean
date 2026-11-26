module
public import LogicLineages.StandardControlCurrent.CollapseFoundationTargets
public import LogicLineages.OrdinalComparison.WWFiniteTailMonotonicityProof
public import LogicLineages.OrdinalComparison.ActualTailSeparation

@[expose] public section
namespace LogicLineages.StandardControlCurrent.CollapseFoundationStatementChecks
open OrdinalComparison

theorem estimates : CollapseFoundationTargets.CollapseEstimates := by
  refine ⟨actualCollapse_controlledStrictness, actualCollapse_finiteValues,
    actualCollapseDominatesNorm, actualCollapseFiniteTailIncrement, ?_⟩
  intro a ha hnon
  let n := Phi (actualOrdinalNorm a)
  have hn : actualOrdinalNorm (n : Ordinal.{0}) = n := by
    have hz : (0 : Ordinal.{0}) < epsilonZero := normalRepresentationSound (NONote.ofNat 0)
    have hn0 : actualOrdinalNorm (0 : Ordinal.{0}) = 0 :=
      actualOrdinalNorm_notationCorrespondence (NONote.ofNat 0)
    have h := (actualFiniteTailClosureNorm 0 hz n).2
    simpa only [zero_add, hn0] using h
  have h := actualCollapse_controlledStrictness a ha (n : Ordinal.{0})
    ((Ordinal.natCast_lt_omega0 n).trans_le hnon) (by rw [hn])
  rw [actualCollapse_finiteValues] at h
  exact h

theorem saturation : CollapseFoundationTargets.LimitSaturation :=
  ⟨actualLimitMaximumPredecessorSaturation, actualLimitMaximumPredecessorStrictGrowth,
    actualMaximumJointMonotone⟩

theorem recurrence : CollapseFoundationTargets.SinglePredecessor :=
  actualSinglePredecessorRecurrence

#print axioms estimates
#print axioms saturation
#print axioms recurrence

end LogicLineages.StandardControlCurrent.CollapseFoundationStatementChecks
