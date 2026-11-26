module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitGraphProof
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitRawProof
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitEffectiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnit.StatementChecks

theorem literal_inflation_sizes : CurrentOneUnitTargets.LiteralInflation := literalInflation
theorem actual_scalar_rows : CurrentOneUnitTargets.ActualScalarRows := actualScalarRows
theorem exact_head_graph : CurrentOneUnitTargets.ExactHeadGraph := exactHeadGraph
theorem exact_selected_graph : CurrentOneUnitTargets.ExactSelectedGraph := exactSelectedGraph
theorem actual_move_codes : CurrentOneUnitTargets.ExactMoveCodes := exactMoveCodes
theorem actual_head_codes : CurrentOneUnitTargets.ExactHeadCodes := exactHeadCodes
theorem actual_selected_codes : CurrentOneUnitTargets.ExactSelectedCodes := exactSelectedCodes
theorem actual_code_effectivity : CurrentOneUnitTargets.Effective := effective

/-- Paper19 lem:one-unit for any selected functional name, literal chosen-policy
ordered source trees, and the same actual current successor control. -/
theorem exact_current_one_unit : CurrentOneUnitTargets.Full :=
  ⟨literal_inflation_sizes,actual_scalar_rows,exact_head_graph,exact_selected_graph,
    actual_move_codes,actual_head_codes,actual_selected_codes,actual_code_effectivity⟩

#print axioms literal_inflation_sizes
#print axioms actual_scalar_rows
#print axioms exact_head_graph
#print axioms exact_selected_graph
#print axioms actual_move_codes
#print axioms actual_head_codes
#print axioms actual_selected_codes
#print axioms actual_code_effectivity
#print axioms exact_current_one_unit

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnit.StatementChecks
