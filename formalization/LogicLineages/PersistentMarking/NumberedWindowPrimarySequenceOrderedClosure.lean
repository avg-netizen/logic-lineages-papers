import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTargets

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceOrderedClosure
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary

theorem orderedRefl (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (qs : NArgs) (types : List Ty) (h : BaseTyped C qs types) :
    OrderedPrimary S K C types qs qs := by
  cases qs with
  | nil => cases h; exact .nil
  | cons Q qs =>
    cases h with
    | cons hq ht => exact .cons (.refl hq) (orderedRefl S K C qs _ ht)
termination_by structural qs

theorem orderedTrans (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (qs rs ts : NArgs) (types : List Ty)
    (h : OrderedPrimary S K C types qs rs) (g : OrderedPrimary S K C types rs ts) :
    OrderedPrimary S K C types qs ts := by
  cases qs with
  | nil => cases h; cases g; exact .nil
  | cons Q qs =>
    cases h with
    | cons hq ht =>
      cases g with
      | cons gr gt => exact .cons (.trans hq gr) (orderedTrans S K C qs _ _ _ ht gt)
termination_by structural qs

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceOrderedClosure
