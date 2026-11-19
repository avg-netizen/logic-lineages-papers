import LogicLineages.PersistentMarking.NumberedWindowArithmeticPairDecodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairChecks
open NumberedWindowArithmeticPairTargets

theorem exact_PairComponentBounds : PairComponentBounds :=
  NumberedWindowArithmeticPairBoundsProof.components

theorem exact_PairInjection : ExactPairInjection :=
  NumberedWindowArithmeticPairBoundsProof.injection

theorem exact_PairDecode : ExactPairDecode :=
  NumberedWindowArithmeticPairDecodeProof.exactDecode

theorem exact_PairRoundtrip : PairRoundtrip :=
  NumberedWindowArithmeticPairDecodeProof.roundtrip

theorem exact_NonPair : ExactNonPair :=
  NumberedWindowArithmeticPairDecodeProof.exactNonPair

#print axioms exact_PairComponentBounds
#print axioms exact_PairInjection
#print axioms exact_PairDecode
#print axioms exact_PairRoundtrip
#print axioms exact_NonPair

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairChecks
