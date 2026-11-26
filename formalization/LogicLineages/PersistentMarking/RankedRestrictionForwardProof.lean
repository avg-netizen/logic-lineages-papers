import LogicLineages.PersistentMarking.RankedRestrictionForwardHeadProof
import LogicLineages.PersistentMarking.RankedRestrictionForwardListProof

namespace LogicLineages.PersistentMarking.RankedRestrictionForwardProof
open Spine RankedRestrictionForwardTargets
open RankedRestrictionForwardHeadProof RankedRestrictionForwardListProof

theorem weak (S : Signature) (q t : Expr) (h : Weak S q t) : WeakMotive S q t := by
  refine Weak.rec (motive_1 := fun q t _ => WeakMotive S q t)
    (motive_2 := fun q t _ => StrictMotive S q t)
    (motive_3 := fun qs ts _ => MatchingMotive S qs ts)
    (motive_4 := fun qs ts _ => MultisetMotive S qs ts)
    (motive_5 := fun qs ts _ => CoverageMotive S qs ts)
    (motive_6 := fun f bs es ts _ => WholeMotive S f bs es ts)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros
    exact var S _ _
  · intros
    exact abs S _ _ _
  · intros
    rename_i hs ht he hTy child ih
    exact funHead S _ _ _ _ he ih
  · intros
    rename_i hs ht child ih
    exact put S _ _ _ ih
  · intros
    rename_i hs ht hi hQ hCall child ih
    exact select S _ _ _ _ _ _ _ _ _ hi hQ hCall ih
  · intros
    exact fabs S _ _ _ _ _ _
  · intros
    rename_i hs ht hP child ih
    exact copy S _ _ _ _ _ hP ih
  · intros
    rename_i hs ht hE multi whole ih ih'
    exact stat S _ _ _ _ _ hE ih ih'
  · intros
    rename_i hs ht hMark child ih
    exact strict S _ _ _ hMark ih
  · exact matchNil S
  · intros
    rename_i hR weak child ih ih'
    exact matchCons S _ _ _ _ _ hR ih ih'
  · intros
    rename_i hS hT hN matchProof coverProof ih ih'
    exact multi S _ _ _ _ _ _ hS hT hN ih ih'
  · intros
    exact coverNil S _
  · intros
    rename_i hAt hStrict child ih ih'
    exact coverCons S _ _ _ _ _ hAt ih ih'
  · intros
    exact wholeNil S _ _ _
  · intros
    rename_i head tail ih ih'
    exact wholeCons S _ _ _ _ _ ih ih'

theorem strictRPO (S : Signature) (q t : Expr) (h : Strict S q t) : StrictMotive S q t := by
  cases h with
  | intro hs ht hMark hW =>
    exact strict S _ _ _ hMark (weak S _ _ hW)

end LogicLineages.PersistentMarking.RankedRestrictionForwardProof
