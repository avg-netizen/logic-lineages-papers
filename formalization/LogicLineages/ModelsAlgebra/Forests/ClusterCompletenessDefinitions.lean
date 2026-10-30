module

public import LogicLineages.ModelsAlgebra.Forests.LeafClusterDefinitions
public import LogicLineages.ModelsAlgebra.Forests.BinaryClusterDefinitions

/-! The literal finite family of descendant-leaf clusters of a forest.
The binary property requires actual disjoint child partitions; it does not
assume maximality, completeness, or any conclusion about host forests. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

noncomputable def finiteLeafCluster (F : FiniteOrderForest) (v : F.Carrier) :
    Finset (ForestLeaf F) := by
  classical
  exact Finset.univ.filter (fun ℓ => v ≤ ℓ.val)

noncomputable def leafClusterFamily (F : FiniteOrderForest) :
    Finset (Finset (ForestLeaf F)) := by
  classical
  exact Finset.univ.image (finiteLeafCluster F)

noncomputable def HasBinaryLeafClusters (F : FiniteOrderForest) : Prop := by
  classical
  exact IsBinaryClusterFamily Finset.univ (leafClusterFamily F)

end LogicLineages.ModelsAlgebra.Forests
