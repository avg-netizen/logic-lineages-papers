module

public import LogicLineages.ModelsAlgebra.Forests.Definitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

/-- Incomparable elements of a forest cannot have a common upper bound. -/
theorem no_common_upper_bound {α : Type*} [PartialOrder α]
    (h : IsOrderForest α) {x y : α}
    (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x) : ¬ ∃ z, x ≤ z ∧ y ≤ z := by
  rintro ⟨z, hxz, hyz⟩
  exact (h hxz hyz).elim hxy hyx

end LogicLineages.ModelsAlgebra.Forests
