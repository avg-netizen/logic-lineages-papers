module

public import LogicLineages.ModelsAlgebra.Forests.Definitions

@[expose] public section

/-! Fixed comparison statements for the elementary forest facts used
in paper 03's width argument. This imports no implementation proofs. -/

namespace LogicLineages.ModelsAlgebra.Forests.Targets

universe u

def incomparableNoCommonUpper : Prop :=
  ∀ (α : Type u) [PartialOrder α], IsOrderForest α →
    ∀ (x y : α), ¬ x ≤ y → ¬ y ≤ x → ¬ ∃ z, x ≤ z ∧ y ≤ z

end LogicLineages.ModelsAlgebra.Forests.Targets
