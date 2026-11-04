module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentationTargets
open DirectMultisetPresentation

def PermutationInvariance : Prop := ∀ (α : Type) (R : α → α → Prop) (source target source' target' : List α), source.Perm source' → target.Perm target' → (Direct R source target ↔ Direct R source' target')

def OccurrenceWitnesses : Prop := ∀ (α : Type) (R : α → α → Prop) (removed inserted : List α), (∀ y ∈ inserted, ∃ z ∈ removed, R z y) ↔ ∃ indices : List Nat, indices.length = inserted.length ∧ Witnesses R removed inserted indices

def MultisetCalibration : Prop := ∀ (α : Type) (R : α → α → Prop) (source target : List α), Direct R source target ↔ MultisetDirect R (source : Multiset α) (target : Multiset α)

def OrderedLibraryCalibration : Prop := ∀ (α : Type) [Preorder α] (R : α → α → Prop), (∀ z y, R z y ↔ y < z) → ∀ source target : List α, Direct R source target ↔ Multiset.IsDershowitzMannaLT (target : Multiset α) (source : Multiset α)

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentationTargets
