module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityTransferDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityTransferTargets
open DirectMultisetAccessibleSubtype DirectMultisetAccessibility

def AccessibleSubtypeAccessibility : Prop := ∀ (α : Type) (R : α → α → Prop)
    (a : AccessibleElement R),
    Acc (fun successor source => LiftedRelation R source successor) a

/-- Only accessibility of the given source's members is assumed, not ambient well-foundedness. -/
def MemberAccessibilityTransfer : Prop := ∀ (α : Type) (R : α → α → Prop)
    (source : List α), MembersAccessible R source → Acc (ReverseDirect R) source

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityTransferTargets
