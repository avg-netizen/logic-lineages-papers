import LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramTargets

import LogicLineages.PersistentMarking.NumberedWindowArithmeticPairChecks
import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramCalibration
open LogicLineages.ComputabilityKnowledge NumberedWindowArithmeticPairProgramTargets

theorem pair (a b : Nat) :
    NumberedWindowArithmeticPair.pair a b = GorbowRegistryTuple.pair a b := rfl

theorem decoder (n : Nat) : NumberedWindowArithmeticPair.decode n = GorbowRegistryDecoder.decodePair n := by
  cases h : NumberedWindowArithmeticPair.decode n with
  | some p =>
    obtain ⟨a,b⟩ := p
    have eq := (NumberedWindowArithmeticPairChecks.exact_PairDecode n a b).mp h
    exact ((GorbowRegistryDecoderProof.pairExact n a b).mpr ((pair a b).symm.trans eq)).symm
  | none =>
    cases hg : GorbowRegistryDecoder.decodePair n with
    | none => rfl
    | some p =>
      obtain ⟨a,b⟩ := p
      have eq := (GorbowRegistryDecoderProof.pairExact n a b).mp hg
      have hs := (NumberedWindowArithmeticPairChecks.exact_PairDecode n a b).mpr ((pair a b).trans eq)
      rw [h] at hs
      cases hs

theorem calibration : PairAndDecodeCalibration := ⟨pair,decoder⟩
end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramCalibration
