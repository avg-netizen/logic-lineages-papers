module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRootDispatchTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticMarkRootChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSelectChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticCopyChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticStatRootChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticBinderRootChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticConcreteRulesProof
open NumberedWindowRootDispatchTargets NumberedWindowArithmeticScalarTargets

theorem calibrated (S : Spine.Signature) (K : List Ty) : RuleCalibration S K
    (NumberedWindowRootDispatchAlgorithm.fixed S.entries (fixed S K).window.2) where
  mark := NumberedWindowArithmeticMarkRootChecks.exact_MarkRoot S K
  lower := NumberedWindowArithmeticMarkRootChecks.exact_LowerRoot S K
  select := NumberedWindowArithmeticSelectChecks.exact_ExactSelectRoot S K
  copy := NumberedWindowArithmeticCopyChecks.exact_ExactCopyRoot S K
  stat := NumberedWindowArithmeticStatRootChecks.exact_ExactStatRoot S K
  fabs := NumberedWindowArithmeticBinderRootChecks.exact_ExactFAbsRoot S K
  beta := NumberedWindowArithmeticBinderRootChecks.exact_ExactBetaRoot S K
  bottom := NumberedWindowArithmeticMarkRootChecks.exact_BottomRoot S K
end LogicLineages.PersistentMarking.NumberedWindowArithmeticConcreteRulesProof
