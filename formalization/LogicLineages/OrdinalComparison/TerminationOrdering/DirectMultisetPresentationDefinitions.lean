module
public import Mathlib.Data.Multiset.DershowitzManna
public import Mathlib.Data.List.Forall2
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentation

/-- Source-to-successor direction. Kept occurrences are literally retained;
removed occurrences are nonempty, inserted occurrences may be empty. -/
def Direct {α : Type} (R : α → α → Prop) (source target : List α) : Prop :=
  ∃ kept removed inserted : List α,
    source.Perm (kept ++ removed) ∧ target.Perm (kept ++ inserted) ∧
    removed ≠ [] ∧ ∀ y ∈ inserted, ∃ z ∈ removed, R z y

/-- Relation-parametric multiset presentation, without any order instance. -/
def MultisetDirect {α : Type} (R : α → α → Prop) (source target : Multiset α) : Prop :=
  ∃ kept removed inserted : Multiset α,
    source = kept + removed ∧ target = kept + inserted ∧
    removed ≠ 0 ∧ ∀ y ∈ inserted, ∃ z ∈ removed, R z y

/-- Each inserted occurrence has its own removed-occurrence index. Reuse is
allowed, exactly as in direct multiset replacement. -/
def Witnesses {α : Type} (R : α → α → Prop) (removed inserted : List α)
    (indices : List Nat) : Prop :=
  List.Forall₂ (fun y i => ∃ z, removed[i]? = some z ∧ R z y) inserted indices

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetPresentation
