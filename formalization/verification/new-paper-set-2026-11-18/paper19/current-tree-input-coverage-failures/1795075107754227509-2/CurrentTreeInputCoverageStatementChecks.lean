module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageRowsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageEffectiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage.StatementChecks

theorem actual_typed_build : CurrentTreeInputCoverageTargets.ActualTypedBuild := typedBuild
theorem actual_tree_codes : CurrentTreeInputCoverageTargets.ActualTreeCodes := treeCodes
theorem actual_raw_program : CurrentTreeInputCoverageTargets.ActualRawProgram := rawProgram

/-- Exact original source trees at every type and binder depth, and the
effective numerical program converting them to actual scoped DAG input. -/
theorem actual_original_tree_input_coverage : CurrentTreeInputCoverageTargets.Full :=
  ⟨actual_typed_build,actual_tree_codes,actual_raw_program⟩

#print axioms actual_typed_build
#print axioms actual_tree_codes
#print axioms actual_raw_program
#print axioms actual_original_tree_input_coverage

end LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage.StatementChecks
