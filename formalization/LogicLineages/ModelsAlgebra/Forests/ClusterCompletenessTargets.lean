module

public import LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessDefinitions

/-! Exact conditional actual-forest cluster suppliers for paper 03 `thm:width`.
Binary splitting is an explicit structural hypothesis still to be proved for
concrete witnesses. No root/meet/leaf preservation is required of embeddings. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def FiniteLeafClusterSemantics : Prop :=
  ∀ (F : FiniteOrderForest) (v : F.Carrier) (ℓ : ForestLeaf F),
    ℓ ∈ finiteLeafCluster F v ↔ ℓ ∈ leafCluster F v

def BinaryForestClusterComplete : Prop :=
  ∀ (F : FiniteOrderForest), HasBinaryLeafClusters F →
    ∀ A : Finset (ForestLeaf F), A.Nonempty →
      (∀ v : F.Carrier, ClusterCompatible A (finiteLeafCluster F v)) →
      ∃ v : F.Carrier, finiteLeafCluster F v = A

def SaturatedHostClusterComplete : Prop :=
  ∀ (F H : FiniteOrderForest) (e : F.Carrier ↪o H.Carrier),
    HasBinaryLeafClusters F →
    (leafFinset H.Carrier).card ≤ (leafFinset F.Carrier).card →
    ∃ b : ForestLeaf F ≃ ForestLeaf H,
      (∀ ℓ, e ℓ.val ≤ (b ℓ).val) ∧
      ∀ w : H.Carrier, ∃ v : F.Carrier,
        ∀ ℓ : ForestLeaf F, w ≤ (b ℓ).val ↔ v ≤ ℓ.val

end LogicLineages.ModelsAlgebra.Forests.Targets
