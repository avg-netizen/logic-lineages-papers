module
public import LogicLineages.OrdinalComparison.KernelProfileLeafProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelProfileLeaf.StatementChecks

theorem fixed_source_growth : Targets.ActualOpenComparisonSourceGrowth := source_growth
theorem fixed_bounded_program : Targets.ActualBoundedKernelProfileLeafProgram := bounded_program
theorem fixed_affine_inputs_program : Targets.ActualAffineKernelIntegerInputsProgram := affine_inputs_program

end LogicLineages.OrdinalComparison.KernelProfileLeaf.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.KernelProfileLeaf
