module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundsDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalBounds.Targets

def LiteralFiniteMaximum : Prop := ∀ (g : Nat → Nat → Nat) (m n : Nat),
  levelBound g m n = (Finset.range m).sup (fun i => (Finset.range (n+1)).sup (g i))
def ComputableBounds : Prop := ∀ (g : Nat → Nat → Nat), Computable₂ g →
  Computable₂ (levelBound g) ∧ Computable (diagonal g)
def FixedLevelPrimitiveRecursive : Prop := ∀ (g : Nat → Nat → Nat),
  (∀ i, Primrec (g i)) → ∀ m, Primrec (levelBound g m)
def MonotoneLevels : Prop := ∀ (g : Nat → Nat → Nat) (n : Nat), Monotone (fun m => levelBound g m n)
def MonotoneInputs : Prop := ∀ (g : Nat → Nat → Nat) (m : Nat), Monotone (levelBound g m)
def DiagonalDominance : Prop := ∀ (g : Nat → Nat → Nat) (m : Nat),
  ∃ N, ∀ n, N ≤ n → levelBound g m n ≤ diagonal g n
def SuccessorTail : Prop := ∀ (g : Nat → Nat → Nat), CoversPR g →
  ∃ m₀, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∀ n, n+1 ≤ levelBound g m n
def EvaderLevelTail : Prop := ∀ (g : Nat → Nat → Nat), CoversPR g →
  ∃ m₀, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∀ k, ∃ N, ∀ n, N ≤ n →
    min k n+2 < levelBound g m n
def EvaderDiagonalTail : Prop := ∀ (g : Nat → Nat → Nat), CoversPR g →
  ∀ k, ∃ N, ∀ n, N ≤ n → min k n+2 < diagonal g n
end LogicLineages.ComputabilityKnowledge.PredictionOriginalBounds.Targets
