module

public import LogicLineages.ModelsAlgebra.Forests.GraphUniversalDefinitions

/-! Exact suppliers for the converse direction of paper 03 `lem:bridge`,
corresponding to the maximal closed-neighborhood argument in paper.tex 81–90.
These do not assert graph representation, uniqueness, Carter's theorem or JEP.
Mathlib `Connected` includes a nonempty vertex type: the empty graph is not
incorrectly required to have a universal vertex. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open GraphBridge

/-- Adjacent vertices in a finite induced-P4/C4-free graph have nested closed
neighborhoods. This is the local obstruction behind the source argument. -/
def AdjacentClosedNeighborhoodsNested : Prop :=
  ∀ (α : Type) [Fintype α] (G : SimpleGraph α),
    ¬ Nonempty (fourPath ↪g G) → ¬ Nonempty (fourCycle ↪g G) →
    ∀ v w, G.Adj v w →
      closedNeighborhood G v ⊆ closedNeighborhood G w ∨
      closedNeighborhood G w ⊆ closedNeighborhood G v

/-- The literal universal-vertex supplier used to recursively represent the
nonempty connected components as order forests. -/
def ConnectedForbiddenHasUniversalVertex : Prop :=
  ∀ (α : Type) [Fintype α] (G : SimpleGraph α),
    ¬ Nonempty (fourPath ↪g G) → ¬ Nonempty (fourCycle ↪g G) →
    G.Connected → ∃ v, ∀ w, w ≠ v → G.Adj v w

end LogicLineages.ModelsAlgebra.Forests.Targets
