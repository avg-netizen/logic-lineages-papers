module

public import LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPair

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithm

theorem pair : NumberedWindowArithmeticPair.pair = NumberedWindowPairAlgorithm.pair := rfl
theorem decode : NumberedWindowArithmeticPair.decode = NumberedWindowPairAlgorithm.decode := rfl

end LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithm
