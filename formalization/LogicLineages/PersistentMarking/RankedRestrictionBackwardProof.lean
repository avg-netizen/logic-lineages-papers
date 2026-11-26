import LogicLineages.PersistentMarking.RankedRestrictionBackwardCases

namespace LogicLineages.PersistentMarking.RankedRestrictionBackwardProof
open Spine RankedRestrictionTargets RankedRestrictionSyntaxProof RankedRestrictionBackwardCases

theorem markedWeak (S : Signature) (q t : Expr) (h : RPO S q t) : MarkedGoal S q t := by
  refine RPO.rec (motive_1 := fun q t _ => MarkedGoal S q t)
    (motive_2 := fun qs ts _ => CoverageGoal S qs ts)
    (motive_3 := fun q ts _ => DominationGoal S q ts)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros
    rename_i hAt he
    exact subtermEq S _ _ _ _ _ hAt he
  · intros
    rename_i hAt child ih
    exact subtermStrict S _ _ _ _ _ hAt ih
  · intros
    rename_i hp hDom ih
    exact precedence S _ _ _ _ hp ih
  · intros
    rename_i hs ht hn he hC hD ihC ihD
    exact multiset S _ _ _ _ _ _ _ hs ht hn he ihC ihD
  · intros
    exact coverNil S _
  · intros
    rename_i hAt hR hC ih ih'
    exact coverCons S _ _ _ _ _ hAt ih ih'
  · intros
    exact domNil S _
  · intros
    rename_i hR hD ih ih'
    exact domCons S _ _ _ ih ih'

theorem strict (S : Signature) (q t : Expr) (h : RPO S q t)
    (hQ : RankedTerm S q) (hT : RankedTerm S t) : Strict S q t :=
  toStrict S q t (markedWeak S q t h) hQ hT

end LogicLineages.PersistentMarking.RankedRestrictionBackwardProof
