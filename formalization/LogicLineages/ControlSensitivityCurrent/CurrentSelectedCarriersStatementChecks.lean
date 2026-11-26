module
public import LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriers.StatementChecks

theorem literal_fresh_position : CurrentSelectedCarriersTargets.ExactFreshRename := exactFreshRename
theorem literal_zero_saturation : CurrentSelectedCarriersTargets.GroundSaturation := groundSaturation
theorem positive_ground_capture_independence : CurrentSelectedCarriersTargets.GroundIndependence := groundIndependence
theorem actual_operator_carriers : CurrentSelectedCarriersTargets.ActualOperators := actualOperators
theorem actual_selected_source_carriers : CurrentSelectedCarriersTargets.EverySelectedHead := everySelectedHead

/-- Paper19 lem:carriers: the selected annotated head has its exact real unary
carrier, with original scalar and actual literal source closure, under the
same arbitrary structural parsing policy and control. -/
theorem exact_current_selected_carriers : CurrentSelectedCarriersTargets.Full :=
  ⟨literal_fresh_position,literal_zero_saturation,positive_ground_capture_independence,
    actual_operator_carriers,actual_selected_source_carriers⟩

#print axioms literal_fresh_position
#print axioms literal_zero_saturation
#print axioms positive_ground_capture_independence
#print axioms actual_operator_carriers
#print axioms actual_selected_source_carriers
#print axioms exact_current_selected_carriers

end LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriers.StatementChecks
