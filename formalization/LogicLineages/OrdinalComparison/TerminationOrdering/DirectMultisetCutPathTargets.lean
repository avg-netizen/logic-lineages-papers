module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathTargets
open DirectMultisetCutPath DirectMultisetPresentation

def ActualSingleOccurrenceCut : Prop := ∀ (α : Type) (R : α → α → Prop)
    (kept inserted : List α) (a : α), (∀ y ∈ inserted, R a y) →
    Relation.CutExpand (fun successor source => R source successor)
      ((kept ++ inserted : List α) : Multiset α) ((kept ++ [a] : List α) : Multiset α)

def ActualDominatedOccurrencePath : Prop := ∀ (α : Type) (R : α → α → Prop)
    (kept removed inserted : List α), (∀ y ∈ inserted, ∃ a ∈ removed, R a y) →
    CutPath R removed.length ((kept ++ removed : List α) : Multiset α) ((kept ++ inserted : List α) : Multiset α)

def ActualDirectPositiveCutPath : Prop := ∀ (α : Type) (R : α → α → Prop) (source target : List α),
    Direct R source target → ∃ k : Nat, 0<k ∧ CutPath R k (source : Multiset α) (target : Multiset α)

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathTargets
