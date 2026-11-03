module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompiler.StatementChecks
theorem exact_fuel : Targets.ExactFuelCompiler := Proof.exactFuel
theorem exact_original_support : Targets.ExactOriginalSupport := Proof.originalSupport
theorem exact_source_row : Targets.ExactSourceRowCompiler := Proof.exactSourceRow
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompiler.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompiler.StatementChecks
