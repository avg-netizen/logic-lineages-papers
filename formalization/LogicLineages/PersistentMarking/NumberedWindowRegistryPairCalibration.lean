module

public import LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRegistryPairCalibration
open LogicLineages.ComputabilityKnowledge

theorem pair : NumberedWindowPairAlgorithm.pair = GorbowRegistryTuple.pair := rfl

theorem decode : NumberedWindowPairAlgorithm.decode = GorbowRegistryDecoder.decodePair := by
  funext n
  unfold NumberedWindowPairAlgorithm.decode GorbowRegistryDecoder.decodePair
  apply congrArg₂ List.find?
  · funext p
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,pair]
  · rfl

end LogicLineages.PersistentMarking.NumberedWindowRegistryPairCalibration
