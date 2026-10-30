module

public import LogicLineages.ModelsAlgebra.Forests.LaminarForestDefinitions
public import LogicLineages.ModelsAlgebra.Forests.TwinRankDefinitions

/-! Recovering the original forest order from actual descendant-leaf clusters
and finite ranks, for the positive-width subdivision construction. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open GraphBridge

def VertexLeafClusterNonempty : Prop :=
  ∀ (F : FiniteOrderForest) (x : F.Carrier), (finiteLeafCluster F x).Nonempty

def OrderReversesLeafClusterInclusion : Prop :=
  ∀ (F : FiniteOrderForest) (x y : F.Carrier), x ≤ y →
    finiteLeafCluster F y ⊆ finiteLeafCluster F x

def LeafClusterEqualityIffNeighborhoodEquality : Prop :=
  ∀ (F : FiniteOrderForest) (x y : F.Carrier),
    finiteLeafCluster F x = finiteLeafCluster F y ↔
      closedNeighborhood (comparabilityGraph F) x = closedNeighborhood (comparabilityGraph F) y

def LeafClusterRankOrderRecovery : Prop :=
  ∀ (F : FiniteOrderForest) (x y : F.Carrier),
    x ≤ y ↔ finiteLeafCluster F y ⊆ finiteLeafCluster F x ∧
      (finiteLeafCluster F x = finiteLeafCluster F y → twinRank F x ≤ twinRank F y)

def TwinRankBelowCarrierCard : Prop :=
  ∀ (F : FiniteOrderForest) (x : F.Carrier), twinRank F x < Fintype.card F.Carrier

def ActualLeafClusterFamilyLaminar : Prop :=
  ∀ F : FiniteOrderForest, IsLaminarLeafFamily (leafClusterFamily F)

end LogicLineages.ModelsAlgebra.Forests.Targets
