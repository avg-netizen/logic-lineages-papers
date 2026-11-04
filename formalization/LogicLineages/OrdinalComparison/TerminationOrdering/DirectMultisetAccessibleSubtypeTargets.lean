module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtypeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtypeTargets
open DirectMultisetPresentation DirectMultisetAccessibleSubtype

def DirectMemberClosure : Prop := ∀ (α : Type) (R : α → α → Prop)
    (source target : List α), MembersAccessible R source → Direct R source target →
    MembersAccessible R target

def OccurrencePreservingLift : Prop := ∀ (α : Type) (R : α → α → Prop)
    (xs : List α), MembersAccessible R xs →
    ∃ lifted : List (AccessibleElement R), lifted.map Subtype.val = xs

def ExactLiftedDirect : Prop := ∀ (α : Type) (R : α → α → Prop)
    (source target : List (AccessibleElement R)),
    Direct (LiftedRelation R) source target ↔
      Direct R (source.map Subtype.val) (target.map Subtype.val)

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtypeTargets
