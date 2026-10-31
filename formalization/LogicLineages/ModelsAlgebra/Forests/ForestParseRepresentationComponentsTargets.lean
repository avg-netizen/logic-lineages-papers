module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponentsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponents.Targets

/-- The supplied concrete fibers are precisely the actual connected components. -/
def FiberReachability : Prop :=
  ∀ (V I : Type) (G : SimpleGraph V) (c : V → I), ConnectedFibers G c →
    ∀ v w, G.Reachable v w ↔ c v = c w

/-- Actual graph isomorphisms recover a permutation of connected pieces and
isomorphisms of their induced graphs. For cotree J roots this is applied to
complements. Full reduced cotree representation/uniqueness remains separate. -/
def FiberIsoRecovery : Prop :=
  ∀ (V W I J : Type) (G : SimpleGraph V) (H : SimpleGraph W)
    (c : V → I) (d : W → J), ConnectedFibers G c → ConnectedFibers H d →
    ∀ f : G ≃g H, ∃ e : I ≃ J,
      (∀ v, d (f v) = e (c v)) ∧
      ∀ i, Nonempty (fiberGraph G c i ≃g fiberGraph H d (e i))

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponents.Targets
