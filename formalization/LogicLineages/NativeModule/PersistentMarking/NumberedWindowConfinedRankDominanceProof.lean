module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConfinedRankDominanceTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConfinedRankMapChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalWellFoundedChecks
public import LogicLineages.PersistentMarking.OrdinalPredecessorClosedRankProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConfinedRankDominanceProof
open Spine NumberedWindowSimulationData NumberedWindowConfinedRankMap
open NumberedWindowConfinedRankMapChecks NumberedWindowConfinedRankDominanceTargets
open NumberedWindowExternalWellFoundedChecks OrdinalPredecessorClosedRankTargets
open OrdinalPredecessorClosedRankProof OrdinalRankSupportProof

theorem exact_ConfinedRankBelowFixedQuote : ConfinedRankBelowFixedQuote := by
  intro S K τ hk q full numerical
  let fullWF : WellFounded (OriginalBelow S) := exact_ConfinedStrictWellFounded S
  let restrictedWF : WellFounded (Restrict (OriginalBelow S) (Guard S K τ)) :=
    InvImage.wf Subtype.val fullWF
  let restricted := restrictedWF.apply q
  have fullRank : full.rank = restricted.rank :=
    exact_PredecessorClosedRankEquality (OriginalBelow S) (Guard S K τ)
      (fun h edge => exact_ConfinedPredecessorInGuard S K τ _ _ h edge) q full restricted
  have quoteMap : ∀ {s t : GuardedTerm S K τ}, Restrict (OriginalBelow S) (Guard S K τ) t s →
      FixedPositiveBelow S K τ (quote t) (quote s) :=
    fun edge => exact_GuardedQuotePreservesStrict S K τ hk _ _ edge
  rw [fullRank]
  exact exact_RankOfRelationMap quote quoteMap restricted numerical

theorem exact_OriginalInitialQuoteRankDominance : OriginalInitialQuoteRankDominance := by
  intro S q τ typed ordinary
  obtain ⟨hk, start, literal⟩ := exact_InitialConfinedWindowGuard S q τ typed ordinary
  let full : WellFounded (OriginalBelow S) := exact_ConfinedStrictWellFounded S
  let numerical : WellFounded (FixedPositiveBelow S (TypeSupport.support q) τ) :=
    exact_ActualPositiveRelationWellFounded S (TypeSupport.support q) [] τ hk
  have initialRank : (full.apply q).rank = (full.apply start.val).rank :=
    congrArg (fun t => (full.apply t).rank) literal.symm
  have bound := exact_ConfinedRankBelowFixedQuote S (TypeSupport.support q) τ hk start
    (full.apply start.val) (numerical.apply (quote start))
  exact ⟨start, full, numerical, literal, initialRank.le.trans bound⟩

#print axioms exact_ConfinedRankBelowFixedQuote
#print axioms exact_OriginalInitialQuoteRankDominance

end LogicLineages.PersistentMarking.NumberedWindowConfinedRankDominanceProof
