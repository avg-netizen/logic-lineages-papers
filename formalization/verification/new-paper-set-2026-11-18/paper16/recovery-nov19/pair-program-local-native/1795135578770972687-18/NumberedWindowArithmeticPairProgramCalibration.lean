module

public import LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramTargets


@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramCalibration
open LogicLineages.ComputabilityKnowledge NumberedWindowArithmeticPairProgramTargets

theorem pair (a b : Nat) :
    NumberedWindowArithmeticPair.pair a b = GorbowRegistryTuple.pair a b := rfl

theorem decoder (n : Nat) : NumberedWindowArithmeticPair.decode n = GorbowRegistryDecoder.decodePair n := by
  unfold NumberedWindowArithmeticPair.decode GorbowRegistryDecoder.decodePair
  apply congrArg₂ List.find?
  · funext p
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,pair]
  · rfl

theorem calibration : PairAndDecodeCalibration := ⟨pair,decoder⟩
end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramCalibration
