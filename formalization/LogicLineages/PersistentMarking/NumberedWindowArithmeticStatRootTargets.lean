import LogicLineages.PersistentMarking.NumberedWindowStatRootAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowArithmeticCopyTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticStatRootTargets
open NumberedWindowStatRootAlgorithm NumberedWindowAdmissionTargets
open NumberedWindowArithmeticMarkRootTargets NumberedWindowArithmeticRawRootCode

def ExactStatRoot : Prop := ∀ S K part,
  stat S.entries (window S K).2 (encodeReplacement part) = rootOn S K (.stat part)

def RejectedStatPartition : Prop := ∀ S K payload, decodeReplacement payload = none →
  ∀ src dst, stat S.entries (window S K).2 payload src dst = false
end LogicLineages.PersistentMarking.NumberedWindowArithmeticStatRootTargets
