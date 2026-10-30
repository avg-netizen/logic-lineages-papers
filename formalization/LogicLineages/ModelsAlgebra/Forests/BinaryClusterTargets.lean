module

public import LogicLineages.ModelsAlgebra.Forests.BinaryClusterDefinitions

/-! Conditional finite combinatorial suppliers for the negative-width argument
in paper 03 `thm:width`. Later concrete forest witnesses must prove the actual
binary-partition hypotheses. No full width classification is asserted here. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def BinaryClusterUniverseNonempty : Prop :=
  ∀ (α : Type) (L : Finset α) (family : Finset (Finset α)),
    IsBinaryClusterFamily L family → L.Nonempty

def BinaryClusterFamilyMaximal : Prop :=
  ∀ (α : Type) (L : Finset α) (family : Finset (Finset α)),
    IsBinaryClusterFamily L family →
    ∀ A : Finset α, A.Nonempty → A ⊆ L →
      (∀ B ∈ family, ClusterCompatible A B) → A ∈ family

end LogicLineages.ModelsAlgebra.Forests.Targets
