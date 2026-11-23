module

public import LogicLineages.PersistentMarking.NumberedWindowCopyAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticOwnerTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowAdmissionTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticCopyTargets
open NumberedWindowCopyAlgorithm NumberedWindowArithmeticHeadCode NumberedWindowArithmeticMarkRootTargets
open NumberedWindowAdmissionTargets NumberedWindowRawWitnessRootBits

def ExactClassRank : Prop := ∀ S f, rank S.entries (encodeHead f) = Spine.classRank S f

def ExactRootRankComparisons : Prop := ∀ S f g,
  compareRanks true S.entries (encodeHead f) (encodeHead g) = precedesBit S f g ∧
  compareRanks false S.entries (encodeHead f) (encodeHead g) = equivalentBit S f g

def ExactCopyRoot : Prop := ∀ S K, copy S.entries (window S K).2 = rootOn S K .copy

end LogicLineages.PersistentMarking.NumberedWindowArithmeticCopyTargets
