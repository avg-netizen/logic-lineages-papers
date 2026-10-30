module

public import LogicLineages.ModelsAlgebra.Forests.TwinRankDefinitions
public import LogicLineages.ModelsAlgebra.Forests.GraphBridgeTargets

/-! Actual uniqueness obligations for paper 03 `lem:bridge`. Graph isomorphisms
transport equal-neighborhood classes; matching their finite chain ranks builds
an order isomorphism, not necessarily the original graph map. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open GraphBridge

def TwinRankSurjective : Prop :=
  ∀ (F : FiniteOrderForest) (x : F.Carrier) (k : Nat), k < twinCard F x →
    ∃! y, y ∈ twinClass F x ∧ twinRank F y = k

def GraphIsoNeighborhoodSubset : Prop :=
  ∀ (F G : FiniteOrderForest) (e : comparabilityGraph F ≃g comparabilityGraph G)
    (x y : F.Carrier),
    closedNeighborhood (comparabilityGraph G) (e x) ⊆
        closedNeighborhood (comparabilityGraph G) (e y) ↔
      closedNeighborhood (comparabilityGraph F) x ⊆ closedNeighborhood (comparabilityGraph F) y

def GraphIsoNeighborhoodEquality : Prop :=
  ∀ (F G : FiniteOrderForest) (e : comparabilityGraph F ≃g comparabilityGraph G)
    (x y : F.Carrier),
    closedNeighborhood (comparabilityGraph G) (e x) =
        closedNeighborhood (comparabilityGraph G) (e y) ↔
      closedNeighborhood (comparabilityGraph F) x = closedNeighborhood (comparabilityGraph F) y

def GraphIsoTwinCard : Prop :=
  ∀ (F G : FiniteOrderForest) (e : comparabilityGraph F ≃g comparabilityGraph G)
    (x : F.Carrier), twinCard G (e x) = twinCard F x

def RankMatchedOrderIso : Prop :=
  ∀ (F G : FiniteOrderForest) (e : comparabilityGraph F ≃g comparabilityGraph G),
    ∃ f : F.Carrier ≃o G.Carrier, ∀ x,
      closedNeighborhood (comparabilityGraph G) (f x) =
          closedNeighborhood (comparabilityGraph G) (e x) ∧
        twinRank G (f x) = twinRank F x

/-- Exactly the existing uniqueness component, with no assumed supplier. -/
def TwinClassOrderUniqueness : Prop := ComparabilityOrderUniqueness

end LogicLineages.ModelsAlgebra.Forests.Targets
