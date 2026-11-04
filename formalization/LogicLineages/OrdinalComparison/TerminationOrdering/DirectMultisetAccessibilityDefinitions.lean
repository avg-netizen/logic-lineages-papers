module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibility

/-- Successor-first accessibility relation on literal lists. -/
def ReverseDirect {α : Type} (R : α → α → Prop) (target source : List α) : Prop :=
  DirectMultisetPresentation.Direct R source target

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibility
