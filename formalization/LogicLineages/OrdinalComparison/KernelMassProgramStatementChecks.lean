module
public import LogicLineages.OrdinalComparison.KernelMassProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelMassProgram.StatementChecks

theorem fixed_primitive : Targets.PrincipalKernelMassProgramPrimitiveRecursive := primitive
theorem fixed_source : Targets.PrincipalKernelMassProgramSource := source
theorem fixed_actual : Targets.ActualPrincipalKernelMassProgram := actual_program

end LogicLineages.OrdinalComparison.KernelMassProgram.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.KernelMassProgram
