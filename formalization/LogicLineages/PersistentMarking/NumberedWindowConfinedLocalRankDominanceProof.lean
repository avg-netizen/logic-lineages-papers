import LogicLineages.PersistentMarking.NumberedWindowConfinedRankDominanceTargets
import LogicLineages.PersistentMarking.NumberedWindowConfinedRankMapChecks
import LogicLineages.PersistentMarking.OrdinalPredecessorClosedRankProof

namespace LogicLineages.PersistentMarking.NumberedWindowConfinedLocalRankDominanceProof
open Spine NumberedWindowConfinedRankMap NumberedWindowConfinedRankMapChecks
open NumberedWindowConfinedRankDominanceTargets
open OrdinalPredecessorClosedRankTargets OrdinalPredecessorClosedRankProof OrdinalRankSupportProof

/-- The exact confined rank inequality needs only the two supplied
accessibility proofs. Restrict the actual source witness along the
subtype projection; no global separation or well-foundedness result is
inserted here. -/
theorem exact_ConfinedRankBelowFixedQuote : ConfinedRankBelowFixedQuote := by
  intro S K τ hk q full numerical
  let restricted : Acc (Restrict (OriginalBelow S) (Guard S K τ)) q :=
    InvImage.accessible (r := OriginalBelow S) (a := q)
      (fun t : GuardedTerm S K τ => t.val) full
  have fullRank : full.rank = restricted.rank :=
    exact_PredecessorClosedRankEquality (OriginalBelow S) (Guard S K τ)
      (fun h edge => exact_ConfinedPredecessorInGuard S K τ _ _ h edge) q full restricted
  have quoteMap : ∀ {s t : GuardedTerm S K τ}, Restrict (OriginalBelow S) (Guard S K τ) t s →
      FixedPositiveBelow S K τ (quote t) (quote s) :=
    fun edge => exact_GuardedQuotePreservesStrict S K τ hk _ _ edge
  rw [fullRank]
  exact exact_RankOfRelationMap quote quoteMap restricted numerical

#print axioms exact_ConfinedRankBelowFixedQuote
end LogicLineages.PersistentMarking.NumberedWindowConfinedLocalRankDominanceProof
