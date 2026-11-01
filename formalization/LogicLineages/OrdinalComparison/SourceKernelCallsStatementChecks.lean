module
public import LogicLineages.OrdinalComparison.SourceKernelCallsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceKernelCalls.StatementChecks

theorem fixed_program : Targets.ActualOuterStripProgram := program
theorem fixed_shape_semantics : Targets.ActualOuterStripShapeSemantics := shape_semantics
theorem fixed_wellFounded : Targets.LiteralPairTransitiveStepWellFounded := transitive_wellFounded
theorem fixed_equal_child : Targets.ActualEqualOuterChildCall := equal_child
theorem fixed_mixed_child : Targets.ActualMixedLimitChildCall := mixed_child
theorem fixed_full : Targets.FullActualOuterKernelChildCalls := full

end LogicLineages.OrdinalComparison.SourceKernelCalls.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.SourceKernelCalls
