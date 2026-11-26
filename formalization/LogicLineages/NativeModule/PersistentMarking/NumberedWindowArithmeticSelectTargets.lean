module

public import LogicLineages.PersistentMarking.NumberedWindowSelectAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticOwnerTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSelectTargets
open NumberedWindowSelectAlgorithm NumberedWindowArithmeticMarkRootTargets
open NumberedWindowArithmeticTyCode

def ExactSelectRoot : Prop := ∀ S K extra i domains,
  select extra i (domains.map encodeTy) = rootOn S K (.select extra i domains)
end LogicLineages.PersistentMarking.NumberedWindowArithmeticSelectTargets
