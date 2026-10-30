module

public import LogicLineages.ModelsAlgebra.Forests.CombForestDefinitions
public import Mathlib.Data.Fintype.Powerset

/-! The complete finite relabeling supplier for the positive-width cases of
paper03 thm:width. All laminar families on n≤m≤3 leaves are quantified, including
empty carriers. The label function is required to be genuinely injective.
This does not yet assert an order embedding of arbitrary forests. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def SmallLaminarCombLabeling : Prop :=
  ∀ m n : Fin 4, n ≤ m →
    ∀ family : Finset (Finset (Fin n.val)), IsLaminarLeafFamily family →
      ∃ f : Fin n.val → Fin m.val, Function.Injective f ∧
        ∀ B ∈ family, B.image f ∈ combFamily m.val

end LogicLineages.ModelsAlgebra.Forests.Targets
