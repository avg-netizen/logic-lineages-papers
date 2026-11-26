module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphNumberedProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphCompilerProgramsProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.StatementChecks

theorem actual_source_S_gate : Targets.ExactS := exactS
theorem actual_whole_open_graph_template : Targets.ExactDirectTemplate := exactDirectTemplate
theorem actual_original_scalar_wire_template : Targets.ExactInsertedTemplate := exactInsertedTemplate
theorem literal_graph_source_template_codes : Targets.ExactTemplateCodes := exactTemplateCodes
theorem actual_ground_boolean_compiler_fibers : Targets.ExactFiberCompiler := exactFiberCompiler
theorem actual_numbered_paid_head_graph : Targets.ExactNumbered := exactNumbered
theorem actual_paid_head_graph_programs : Targets.EffectiveHeadGraph := effectiveHeadGraph

/-- Paper19 thm:head-graph, from an arbitrary actual paid certificate. -/
theorem complete_whole_paid_head_graph : Targets.Full :=
  ⟨FoundationStatementChecks.actual_paid_head_foundation,UnitCodeStatementChecks.actual_unit_code_support,
    actual_source_S_gate,actual_whole_open_graph_template,actual_original_scalar_wire_template,
    literal_graph_source_template_codes,actual_ground_boolean_compiler_fibers,actual_numbered_paid_head_graph,
    actual_paid_head_graph_programs⟩

#print axioms actual_source_S_gate
#print axioms actual_whole_open_graph_template
#print axioms actual_original_scalar_wire_template
#print axioms literal_graph_source_template_codes
#print axioms actual_ground_boolean_compiler_fibers
#print axioms actual_numbered_paid_head_graph
#print axioms actual_paid_head_graph_programs
#print axioms complete_whole_paid_head_graph

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.StatementChecks
