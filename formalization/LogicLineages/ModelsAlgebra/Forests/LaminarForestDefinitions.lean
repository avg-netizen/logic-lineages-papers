module

public import LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessDefinitions

/-! Concrete finite laminar-family data for forest witnesses. No representation
or leaf correctness theorem is included in this predicate. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

noncomputable def IsLaminarLeafFamily {α : Type} (family : Finset (Finset α)) : Prop := by
  classical
  exact (∀ B ∈ family, B.Nonempty) ∧
    (∀ a : α, {a} ∈ family) ∧
    ∀ B ∈ family, ∀ C ∈ family, ClusterCompatible B C

end LogicLineages.ModelsAlgebra.Forests
