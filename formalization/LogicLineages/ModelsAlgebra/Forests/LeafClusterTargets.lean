module

public import LogicLineages.ModelsAlgebra.Forests.LeafClusterDefinitions

/-! Source suppliers for paper 03 `thm:width`, the saturation/cluster argument.
The host/source are actual finite order forests and the map is an ordinary
order embedding. No leaf/root/meet preservation is assumed. Empty forests
are included. These contracts do not assert the full width classification. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def LeafClustersLaminar : Prop :=
  ∀ (F : FiniteOrderForest) (u v : F.Carrier),
    leafCluster F u ⊆ leafCluster F v ∨ leafCluster F v ⊆ leafCluster F u ∨
      Disjoint (leafCluster F u) (leafCluster F v)

def SaturatedLeafBijection : Prop :=
  ∀ (F H : FiniteOrderForest) (e : F.Carrier ↪o H.Carrier),
    (leafFinset H.Carrier).card ≤ (leafFinset F.Carrier).card →
    ∃ b : ForestLeaf F ≃ ForestLeaf H, ∀ ℓ, e ℓ.val ≤ (b ℓ).val

def SaturatedClusterTransport : Prop :=
  ∀ (F H : FiniteOrderForest) (e : F.Carrier ↪o H.Carrier),
    (leafFinset H.Carrier).card ≤ (leafFinset F.Carrier).card →
    ∃ b : ForestLeaf F ≃ ForestLeaf H,
      (∀ ℓ, e ℓ.val ≤ (b ℓ).val) ∧
      ∀ (v : F.Carrier) (ℓ : ForestLeaf F),
        b ℓ ∈ leafCluster H (e v) ↔ ℓ ∈ leafCluster F v

end LogicLineages.ModelsAlgebra.Forests.Targets
