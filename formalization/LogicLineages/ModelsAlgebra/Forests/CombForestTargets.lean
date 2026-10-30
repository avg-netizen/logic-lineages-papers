module

public import LogicLineages.ModelsAlgebra.Forests.CombForestDefinitions

/-! Concrete source comb obligations for the negative-width proof in paper03.
The actual forest witness is constructed, not assumed. Full width classification
and the incompatible second source remain separate obligations. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def CombFamilyBinary : Prop :=
  ∀ m : Nat, 0 < m → IsBinaryClusterFamily Finset.univ (combFamily m)

def CombNontrivialClustersNested : Prop :=
  ∀ (m : Nat) (A B : Finset (Fin m)), A ∈ combFamily m → B ∈ combFamily m →
    2 ≤ A.card → 2 ≤ B.card → A ⊆ B ∨ B ⊆ A

def ActualCombForest : Prop :=
  ∀ m : Nat, 0 < m → ∃ F : FiniteOrderForest,
    HasBinaryLeafClusters F ∧ (leafFinset F.Carrier).card = m ∧
    ∀ u v : F.Carrier,
      2 ≤ (finiteLeafCluster F u).card → 2 ≤ (finiteLeafCluster F v).card →
        finiteLeafCluster F u ⊆ finiteLeafCluster F v ∨
          finiteLeafCluster F v ⊆ finiteLeafCluster F u

end LogicLineages.ModelsAlgebra.Forests.Targets
