import LogicLineages.PersistentMarking.NumberedWindowClosingTraceThinProof
import LogicLineages.PersistentMarking.NumberedWindowClosingTypedThinProof
import LogicLineages.PersistentMarking.NumberedWindowClosingRealizationProof
import LogicLineages.PersistentMarking.NumberedWindowClosingAbsProof
import LogicLineages.PersistentMarking.NumberedWindowClosingFAbsProof
import LogicLineages.PersistentMarking.NumberedWindowFrameInclusionProof

namespace LogicLineages.PersistentMarking.NumberedWindowFrameThinChecks
open NumberedWindowFrameTargets

theorem exact_ClosingInventories : ClosingInventories :=
  NumberedWindowClosingInventoryProof.term

theorem exact_ClosingLexicalAdmissibility : ClosingLexicalAdmissibility := by
  intro S K n d C D τ q hc h
  exact NumberedWindowClosingTypedThinProof.admissible hc h

theorem exact_ClosingBetaCommutes : ClosingBetaCommutes :=
  NumberedWindowClosingBetaProof.term

theorem exact_ClosingRaw : ClosingRaw := by
  intro S K n d q r h
  exact NumberedWindowClosingRawProof.term n h d

theorem exact_ClosingPrimary : ClosingPrimary := by
  intro S K n d C D τ q r hc h
  exact NumberedWindowClosingPrimaryThinProof.term n h d D hc

theorem exact_ClosingTypedTrace : ClosingTypedTrace := by
  intro S K n d C D τ q r hc tr
  exact NumberedWindowClosingTraceThinProof.trace hc tr

theorem exact_ClosingRealization : ClosingRealization := by
  intro n name q Q h
  exact NumberedWindowClosingRealizationProof.term name h 0

theorem exact_ClosingRecoversAbsBody : ClosingRecoversAbsBody :=
  NumberedWindowClosingAbsProof.absBody

theorem exact_ClosingRecoversFAbsBody : ClosingRecoversFAbsBody :=
  NumberedWindowClosingFAbsProof.ownerBody

theorem exact_EnlargingAdmissibility : EnlargingAdmissibility := by
  intro S K L C τ q h hq
  exact NumberedWindowFrameInclusionProof.admitted h hq

theorem exact_EnlargingRaw : EnlargingRaw := by
  intro S K L q r h hs
  exact NumberedWindowFrameInclusionProof.raw h hs

theorem exact_EnlargingPrimary : EnlargingPrimary := by
  intro S K L C τ q r h he
  exact NumberedWindowFrameInclusionProof.primary h he

theorem exact_EnlargingTypedTrace : EnlargingTypedTrace := by
  intro S K L C τ q r h tr
  exact NumberedWindowFrameInclusionProof.trace h tr

#print axioms exact_ClosingInventories
#print axioms exact_ClosingLexicalAdmissibility
#print axioms exact_ClosingBetaCommutes
#print axioms exact_ClosingRaw
#print axioms exact_ClosingPrimary
#print axioms exact_ClosingTypedTrace
#print axioms exact_ClosingRealization
#print axioms exact_ClosingRecoversAbsBody
#print axioms exact_ClosingRecoversFAbsBody
#print axioms exact_EnlargingAdmissibility
#print axioms exact_EnlargingRaw
#print axioms exact_EnlargingPrimary
#print axioms exact_EnlargingTypedTrace

end LogicLineages.PersistentMarking.NumberedWindowFrameThinChecks
