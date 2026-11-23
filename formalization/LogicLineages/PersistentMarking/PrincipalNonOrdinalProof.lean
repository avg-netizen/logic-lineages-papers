import LogicLineages.PersistentMarking.PrincipalNonOrdinalTargets
import LogicLineages.PersistentMarking.ProtectedSpineDecisionSplitChecks
import LogicLineages.PersistentMarking.StablePairChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalWellFoundedChecks
import LogicLineages.PersistentMarking.NativeOrientationChecks
import LogicLineages.PersistentMarking.RankedRestrictionChecks

namespace LogicLineages.PersistentMarking.PrincipalNonOrdinalProof
open PrincipalNonOrdinalTargets

theorem decision : Decision := by
  intro S s t σ τ hs os ht ot
  exact (ProtectedSpineDecisionSplitChecks.exact_Decidability S s t σ τ hs os ht ot).2.2

theorem orderLaws : OrderLaws := by
  obtain ⟨refl,weakTrans,inclusion,strictTrans,weakStrict,strictWeak,_,_,_,_⟩ :=
    StablePairChecks.exact_fullStablePair
  exact ⟨refl,weakTrans,strictTrans,
    NumberedWindowExternalWellFoundedChecks.exact_ConfinedStrictWellFounded,
    inclusion,weakStrict,strictWeak⟩

theorem structural : Structural := by
  obtain ⟨_,_,_,_,_,_,weakSub,strictSub,weakCtx,strictCtx⟩ :=
    StablePairChecks.exact_fullStablePair
  exact ⟨weakCtx,strictCtx,weakSub,strictSub⟩

theorem orientation : Orientation := NativeOrientationChecks.exact_fullOrientation

theorem ranked : Ranked := by
  intro S s t hs ht
  exact (RankedRestrictionChecks.exact_ExactRankedRestriction S s t hs ht).1

theorem principalNonOrdinal : PrincipalNonOrdinal :=
  ⟨decision,orderLaws,structural,orientation,ranked⟩

end LogicLineages.PersistentMarking.PrincipalNonOrdinalProof
