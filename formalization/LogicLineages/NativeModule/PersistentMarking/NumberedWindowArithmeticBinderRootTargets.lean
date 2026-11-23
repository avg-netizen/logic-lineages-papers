module

public import LogicLineages.PersistentMarking.NumberedWindowBinderRootAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticMarkRootTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderRootTargets
open NumberedWindowBinderRootAlgorithm NumberedWindowArithmeticMarkRootTargets

def ExactFAbsRoot : Prop := ∀ S K, fabs = rootOn S K .fabs
def ExactBetaRoot : Prop := ∀ S K, beta = rootOn S K .beta

end LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderRootTargets
