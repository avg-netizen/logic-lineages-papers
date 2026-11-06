module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeTargetChecks
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeEqualityProof
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedSupplierStatementChecks
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeStatementChecks

theorem shifted_source_budget_order : Targets.ShiftedSourceBudgetOrder :=
  Proof.shiftedSourceBudgetOrder

theorem broad_source_block : Targets.BroadSourceBlock := Proof.broadSourceBlock

theorem cubic_unsigned_separation : Targets.CubicUnsignedSeparation :=
  Proof.cubicUnsignedSeparation

theorem unsigned_separation : Targets.UnsignedSeparation := Proof.unsignedSeparation

theorem quantitative_separation : Targets.QuantitativeSeparation := Proof.quantitativeSeparation

theorem effective_equality_tail : Targets.EffectiveEqualityTail := Proof.effectiveEqualityTail

theorem uniform_depth_and_output_bounds : Targets.UniformDepthAndOutputBounds :=
  Focused.uniformDepthAndOutputBounds

theorem full_uniform_source : Targets.FullUniformSource := Proof.fullUniformSource

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeStatementChecks

#audit_namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeStatementChecks
