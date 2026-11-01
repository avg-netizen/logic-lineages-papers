module
public import LogicLineages.OrdinalComparison.KernelInputProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelInputProgram.StatementChecks

theorem fixed_strict : Targets.ActualPrincipalKernelStrictInputs := strict_inputs
theorem fixed_primitive : Targets.PrincipalKernelInputProgramPrimitiveRecursive := primitive
theorem fixed_actual : Targets.ActualPrincipalKernelInputProgram := actual_program

end LogicLineages.OrdinalComparison.KernelInputProgram.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.KernelInputProgram
