module

public import LogicLineages.ModelsAlgebra.Forests.CanonicalOrderDefinitions
public import LogicLineages.ModelsAlgebra.Forests.GraphBridgeTargets

/-! Exact reverse-representation obligations, paper 03 `lem:bridge`.
All finite graphs, including empty and singleton graphs, are in the domain.
The explicit relation supplies an actual partial order only after its laws are
proved. Uniqueness and reverse embedding reflection are not asserted here. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open GraphBridge

def CanonicalPartialOrderLaws : Prop :=
  ∀ (α : Type) [Fintype α] (G : SimpleGraph α),
    (∀ x, canonicalLE G x x) ∧
    (∀ x y z, canonicalLE G x y → canonicalLE G y z → canonicalLE G x z) ∧
    (∀ x y, canonicalLE G x y → canonicalLE G y x → x = y)

def CanonicalPredecessorsChain : Prop :=
  ∀ (α : Type) [Fintype α] (G : SimpleGraph α),
    ¬ Nonempty (fourPath ↪g G) → ¬ Nonempty (fourCycle ↪g G) →
    ∀ x y z, canonicalLE G x z → canonicalLE G y z →
      canonicalLE G x y ∨ canonicalLE G y x

def CanonicalAdjacencyComparability : Prop :=
  ∀ (α : Type) [Fintype α] (G : SimpleGraph α),
    ¬ Nonempty (fourPath ↪g G) → ¬ Nonempty (fourCycle ↪g G) →
    ∀ x y, G.Adj x y ↔ x ≠ y ∧ (canonicalLE G x y ∨ canonicalLE G y x)

/-- The existing full graph-representation component, not a weakened surrogate. -/
def CanonicalGraphRepresentation : Prop := ComparabilityGraphRepresentation

end LogicLineages.ModelsAlgebra.Forests.Targets
