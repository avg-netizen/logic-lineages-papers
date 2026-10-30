module

public import LogicLineages.ModelsAlgebra.Forests.WidthJEPDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessDefinitions

/-! The negative half of paper03 thm:width, with actual concrete witnesses.
The generic obstruction's structural hypotheses are separately proved for
those witnesses. Positive small-width cases are not asserted here. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def ClusterCommonHostObstruction : Prop :=
  ∀ F G : FiniteOrderForest, HasBinaryLeafClusters F →
    (leafFinset F.Carrier).card = (leafFinset G.Carrier).card →
    (∀ u v : F.Carrier,
      2 ≤ (finiteLeafCluster F u).card → 2 ≤ (finiteLeafCluster F v).card →
      finiteLeafCluster F u ⊆ finiteLeafCluster F v ∨
        finiteLeafCluster F v ⊆ finiteLeafCluster F u) →
    (∃ u v : G.Carrier,
      Disjoint (finiteLeafCluster G u) (finiteLeafCluster G v) ∧
      2 ≤ (finiteLeafCluster G u).card ∧ 2 ≤ (finiteLeafCluster G v).card) →
    ¬ ∃ H : FiniteOrderForest,
      WidthAtMost H.Carrier (leafFinset F.Carrier).card ∧
      Nonempty (F.Carrier ↪o H.Carrier) ∧ Nonempty (G.Carrier ↪o H.Carrier)

def WidthAtLeastFourFailsJEP : Prop :=
  ∀ m : Nat, 4 ≤ m → ¬ WidthHasJEP m

end LogicLineages.ModelsAlgebra.Forests.Targets
