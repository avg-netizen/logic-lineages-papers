module

public import Mathlib.Data.Finset.Card

/-! Finite binary cluster families for paper 03 `thm:width`.
Maximality is not part of the data. Every cluster is nonempty, so the universe
is necessarily nonempty; the empty-forest width-zero case is separate. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

def ClusterCompatible {α : Type} (A B : Finset α) : Prop :=
  A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

noncomputable def IsBinaryClusterFamily {α : Type} (L : Finset α)
    (family : Finset (Finset α)) : Prop := by
  classical
  exact L ∈ family ∧
    (∀ B ∈ family, B.Nonempty ∧ B ⊆ L) ∧
    (∀ x ∈ L, {x} ∈ family) ∧
    (∀ B ∈ family, ∀ C ∈ family, ClusterCompatible B C) ∧
    ∀ B ∈ family, B.card = 1 ∨
      ∃ C ∈ family, ∃ D ∈ family,
        C.Nonempty ∧ D.Nonempty ∧ Disjoint C D ∧ C ∪ D = B

end LogicLineages.ModelsAlgebra.Forests
