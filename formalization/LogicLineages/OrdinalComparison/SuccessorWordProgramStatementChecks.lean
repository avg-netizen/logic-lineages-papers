module
public import LogicLineages.OrdinalComparison.SuccessorWordProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SuccessorWordProgram.StatementChecks

theorem fixed_primitive : Targets.SuccessorWordProgramsPrimitiveRecursive := primitive
theorem fixed_source : Targets.SuccessorWordProgramsSource := source
theorem fixed_actual : Targets.ActualSuccessorWordProgram := actual_program

end LogicLineages.OrdinalComparison.SuccessorWordProgram.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SuccessorWordProgram
