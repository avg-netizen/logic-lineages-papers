module
public import LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAffineHeads.StatementChecks

theorem actual_positive_collapse_exclusion : CurrentAffineHeadsTargets.PositiveNoCollapse := positiveNoCollapse
theorem actual_common_unit_valuation : CurrentAffineHeadsTargets.SameCommonUnits := sameCommonUnits
theorem actual_head_partial_finite_surplus : CurrentAffineHeadsTargets.ActualHead := actualHead
theorem actual_selected_source_affine_heads : CurrentAffineHeadsTargets.CompleteSource := completeSource

/-- Paper19 lem:affine-head, with every real selected head and its own tail
under the same arbitrary selected source parsing policy and control. -/
theorem exact_current_affine_heads : CurrentAffineHeadsTargets.Full :=
  ⟨actual_positive_collapse_exclusion,actual_common_unit_valuation,
    actual_head_partial_finite_surplus,actual_selected_source_affine_heads⟩

#print axioms actual_positive_collapse_exclusion
#print axioms actual_common_unit_valuation
#print axioms actual_head_partial_finite_surplus
#print axioms actual_selected_source_affine_heads
#print axioms exact_current_affine_heads

end LogicLineages.ControlSensitivityCurrent.CurrentAffineHeads.StatementChecks
