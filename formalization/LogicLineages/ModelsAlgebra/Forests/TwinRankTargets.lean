module

public import LogicLineages.ModelsAlgebra.Forests.TwinRankDefinitions

/-! Order-recovery suppliers for the uniqueness clause of paper 03 `lem:bridge`.
The original forest order is retained; the numerical rank counts actual strict
predecessors within its literal equal-neighborhood class. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open GraphBridge

def OrderReversesNeighborhoodInclusion : Prop :=
  ∀ (F : FiniteOrderForest) (x y : F.Carrier), x ≤ y →
    closedNeighborhood (comparabilityGraph F) y ⊆ closedNeighborhood (comparabilityGraph F) x

def TwinClassChain : Prop :=
  ∀ (F : FiniteOrderForest) (x y : F.Carrier),
    closedNeighborhood (comparabilityGraph F) x = closedNeighborhood (comparabilityGraph F) y →
    x ≤ y ∨ y ≤ x

def TwinRankOrder : Prop :=
  ∀ (F : FiniteOrderForest) (x y : F.Carrier),
    closedNeighborhood (comparabilityGraph F) x = closedNeighborhood (comparabilityGraph F) y →
    (x ≤ y ↔ twinRank F x ≤ twinRank F y)

def TwinRankOrderRecovery : Prop :=
  ∀ (F : FiniteOrderForest) (x y : F.Carrier),
    x ≤ y ↔
      closedNeighborhood (comparabilityGraph F) y ⊆ closedNeighborhood (comparabilityGraph F) x ∧
      (closedNeighborhood (comparabilityGraph F) x = closedNeighborhood (comparabilityGraph F) y →
        twinRank F x ≤ twinRank F y)

def TwinRankBound : Prop :=
  ∀ (F : FiniteOrderForest) (x : F.Carrier), twinRank F x < twinCard F x

end LogicLineages.ModelsAlgebra.Forests.Targets
