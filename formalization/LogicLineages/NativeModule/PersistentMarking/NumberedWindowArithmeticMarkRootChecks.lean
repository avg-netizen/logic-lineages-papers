module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticMarkRootProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootChecks
open NumberedWindowArithmeticMarkRootTargets NumberedWindowArithmeticMarkRootProof
theorem exact_MarkRoot : ExactMarkRoot := markEq
theorem exact_LowerRoot : ExactLowerRoot := lowerEq
theorem exact_BottomRoot : ExactBottomRoot := bottomEq
#print axioms exact_MarkRoot
#print axioms exact_LowerRoot
#print axioms exact_BottomRoot
end LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootChecks
