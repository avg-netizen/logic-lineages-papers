module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtype

def AccessibleElement {α : Type} (R : α → α → Prop) :=
  {a : α // Acc (fun successor source => R source successor) a}

def LiftedRelation {α : Type} (R : α → α → Prop)
    (source successor : AccessibleElement R) : Prop := R source.val successor.val

def MembersAccessible {α : Type} (R : α → α → Prop) (xs : List α) : Prop :=
  ∀ a ∈ xs, Acc (fun successor source => R source successor) a

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtype
