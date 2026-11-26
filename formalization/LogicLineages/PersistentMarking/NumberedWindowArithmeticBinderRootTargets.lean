import LogicLineages.PersistentMarking.NumberedWindowBinderRootAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderRootTargets
open NumberedWindowBinderRootAlgorithm NumberedWindowArithmeticMarkRootTargets

def ExactFAbsRoot : Prop := ∀ S K, fabs = rootOn S K .fabs
def ExactBetaRoot : Prop := ∀ S K, beta = rootOn S K .beta

end LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderRootTargets
