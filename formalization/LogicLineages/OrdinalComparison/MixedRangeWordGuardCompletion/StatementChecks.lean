module
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.QuadraticProof
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.MeasureProof
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.StatementChecks

theorem fixed_mixedKernelGuard : Targets.MixedKernelGuard := Proof.mixedKernelGuard
theorem fixed_mixedQuadraticGuard : Targets.MixedQuadraticGuard := Proof.mixedQuadraticGuard
theorem fixed_mixedHeadDecrease : Targets.MixedHeadDecrease := Proof.mixedHeadDecrease
theorem fixed_guardPrograms : Targets.GuardPrograms := Proof.guardPrograms

#print axioms fixed_mixedKernelGuard
#print axioms fixed_mixedQuadraticGuard
#print axioms fixed_mixedHeadDecrease
#print axioms fixed_guardPrograms

end LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.StatementChecks
