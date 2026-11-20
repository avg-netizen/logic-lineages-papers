import LogicLineages.PersistentMarking.NumberedWindowSelectAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowArithmeticOwnerTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSelectTargets
open NumberedWindowSelectAlgorithm NumberedWindowArithmeticMarkRootTargets
open NumberedWindowArithmeticTyCode

def ExactSelectRoot : Prop := ∀ S K extra i domains,
  select extra i (domains.map encodeTy) = rootOn S K (.select extra i domains)
end LogicLineages.PersistentMarking.NumberedWindowArithmeticSelectTargets
