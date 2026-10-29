module

public import LogicLineages.ModelsAlgebra.Forests.WidthDefinitions
public import LogicLineages.ModelsAlgebra.Forests.OrderFacts
public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-!
# Width equals the number of leaves

The proof constructs a maximal extension of each antichain vertex and
proves that two distinct antichain vertices cannot choose the same leaf.
No injection or maximal-extension supplier is assumed as an input.
-/

namespace LogicLineages.ModelsAlgebra.Forests

variable {α : Type*} [PartialOrder α] [Fintype α]

@[simp] theorem mem_leafFinset {x : α} : x ∈ leafFinset α ↔ IsMax x := by
  classical
  simp [leafFinset]

theorem exists_leaf_above (x : α) : ∃ y, x ≤ y ∧ IsMax y := by
  obtain ⟨y, hxy, hy⟩ :=
    Finite.exists_le_maximal (p := fun _ : α => True) (a := x) trivial
  refine ⟨y, hxy, ?_⟩
  intro z hyz
  exact hy.2 trivial hyz

theorem leafFinset_isAntichain : IsAntichain (· ≤ ·) (leafFinset α : Set α) := by
  intro x hx y hy hne hxy
  exact hne (le_antisymm hxy ((mem_leafFinset.mp hx) hxy))

theorem antichain_card_le_leaf_card (hForest : IsOrderForest α)
    (s : Finset α) (hs : IsAntichain (· ≤ ·) (s : Set α)) :
    s.card ≤ (leafFinset α).card := by
  classical
  let f : α → α := fun x => (exists_leaf_above x).choose
  have hf_le : ∀ x, x ≤ f x := fun x => (exists_leaf_above x).choose_spec.1
  have hf_leaf : ∀ x, IsMax (f x) := fun x => (exists_leaf_above x).choose_spec.2
  have hinj : Set.InjOn f (s : Set α) := by
    intro x hx y hy hEq
    by_contra hne
    apply no_common_upper_bound hForest
      (fun hxy => hne (hs.eq hx hy hxy))
      (fun hyx => hne (hs.eq' hx hy hyx))
    refine ⟨f x, hf_le x, ?_⟩
    rw [hEq]
    exact hf_le y
  have hsub : s.image f ⊆ leafFinset α := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact mem_leafFinset.mpr (hf_leaf x)
  calc
    s.card = (s.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (leafFinset α).card := Finset.card_le_card hsub

theorem widthAtMost_iff_leaf_card (hForest : IsOrderForest α) (m : ℕ) :
    WidthAtMost α m ↔ (leafFinset α).card ≤ m := by
  constructor
  · intro hWidth
    exact hWidth _ leafFinset_isAntichain
  · intro hLeaves s hs
    exact (antichain_card_le_leaf_card hForest s hs).trans hLeaves

end LogicLineages.ModelsAlgebra.Forests
