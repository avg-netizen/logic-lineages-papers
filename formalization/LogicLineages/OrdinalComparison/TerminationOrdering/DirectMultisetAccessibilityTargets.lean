module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityTargets
open DirectMultisetCutPath DirectMultisetAccessibility

def PositivePathTransGen : Prop := ∀ (α : Type) (R : α → α → Prop)
    (k : Nat) (source target : Multiset α), 0 < k → CutPath R k source target →
    Relation.TransGen (Relation.CutExpand (fun successor source => R source successor)) target source

/-- The global irreflexivity hypothesis is explicit, not derived from member accessibility. -/
def IrreflexiveMemberAccessibility : Prop := ∀ (α : Type) (R : α → α → Prop),
    (∀ a, ¬ R a a) → ∀ source : List α,
    (∀ a ∈ source, Acc (fun successor source => R source successor) a) →
    Acc (ReverseDirect R) source

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibilityTargets
