module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowActualPairAlgorithm

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithmChecks

theorem currentPair : NumberedWindowArithmeticPair.pair = NumberedWindowPairAlgorithm.pair :=
  NumberedWindowActualPairAlgorithm.pair

theorem currentDecoder : NumberedWindowArithmeticPair.decode = NumberedWindowPairAlgorithm.decode :=
  NumberedWindowActualPairAlgorithm.decode

#print axioms currentPair
#print axioms currentDecoder
end LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithmChecks
