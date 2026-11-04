module
public import LogicLineages.OrdinalComparison.ParametricFinitePairCollapseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricFinitePairCollapse.Targets

def ExactRepresentation : Prop :=
  (∀ p : Nat × Nat, ordinal p < epsilonZero ∧ actualOrdinalNorm (ordinal p)=pairNorm p) ∧
  Function.Injective ordinal ∧
  (∀ (p : Nat × Nat) (x : Ordinal.{0}), x < ordinal p ↔
    ∃ q : Nat × Nat, Below q p ∧ x=ordinal q)

def ExactPredecessors : Prop := ∀ (G : Nat → Nat) (p : Nat × Nat) (x : Ordinal.{0}),
  x ∈ actualBoundedPredecessors (ordinal p) (G (actualOrdinalNorm (ordinal p))) ↔
    ∃ q ∈ predecessors G p, x=ordinal q

def ExactMaximum : Prop := ∀ (G : Nat → Nat) (p : Nat × Nat),
  value G p = (predecessors G p).sup (fun q => value G q+1)
end LogicLineages.OrdinalComparison.Source.ParametricFinitePairCollapse.Targets
