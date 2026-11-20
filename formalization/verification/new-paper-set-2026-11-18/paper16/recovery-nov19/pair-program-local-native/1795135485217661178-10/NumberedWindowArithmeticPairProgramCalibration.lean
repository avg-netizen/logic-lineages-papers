import LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramCalibration
open LogicLineages.ComputabilityKnowledge NumberedWindowArithmeticPairProgramTargets

theorem pair (a b : Nat) :
    NumberedWindowArithmeticPair.pair a b = GorbowRegistryTuple.pair a b := rfl

theorem decoder (n : Nat) : NumberedWindowArithmeticPair.decode n = GorbowRegistryDecoder.decodePair n := by
  unfold NumberedWindowArithmeticPair.decode GorbowRegistryDecoder.decodePair
  unfold NumberedWindowArithmeticPair.pairCandidates GorbowRegistryDecoder.pairCandidates
  simp only [pair]

theorem calibration : PairAndDecodeCalibration := ⟨pair,decoder⟩
end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramCalibration
