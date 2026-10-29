module

public import LogicLineages.ModelsAlgebra.Forests.Definitions
public import Mathlib.Order.Antichain
public import Mathlib.Order.Max
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Width and leaves of an actual finite partial order

Paper 03 defines width by antichain size and calls maximal vertices
leaves. The definitions here express those two independent notions;
their equality for forests is a proof obligation, not a definition.
-/

namespace LogicLineages.ModelsAlgebra.Forests

def WidthAtMost (α : Type*) [PartialOrder α] (m : ℕ) : Prop :=
  ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ m

noncomputable def leafFinset (α : Type*) [PartialOrder α] [Fintype α] : Finset α := by
  classical
  exact Finset.univ.filter IsMax

end LogicLineages.ModelsAlgebra.Forests
