module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalHardnessDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalHardnessTargets
open PredictionTapeObservation PredictionTapeRuntimeClass PredictionOriginalBounds PredictionOriginalHardness

def SimultaneousOriginalReduction : Prop :=
  ∀ g : Nat → Nat → Nat, OriginalListing g →
    ∃ m₀ : Nat, 1 ≤ m₀ ∧ ∀ R : PredictionFiniteChange.Matrix, Computable R →
      ∃ f : Nat → Nat, Computable f ∧ ∃ hp : ∀ z : Nat, TotalBinary (f z),
        ∀ z : Nat,
          (Threshold (policy (f z) (hp z)) (diagonal g) ↔ MatrixTruth R z) ∧
          (originalHeight g (policy (f z) (hp z)) = ⊤ ↔ MatrixTruth R z) ∧
          (∀ m : Nat, m₀ ≤ m → (Threshold (policy (f z) (hp z)) (levelBound g m) ↔ MatrixTruth R z))

/-- Both source proposition clauses, including the same-family original-list
specialization. The source's fixed listing is represented by its explicit
uniform total evaluator / entry-PR / coverage requirements. -/
def WholeSourceHardness : Prop :=
  PredictionTapeHardnessTargets.FixedBudgetHardness ∧ SimultaneousOriginalReduction

def InfiniteOriginalPredictor : Prop :=
  ∀ g : Nat → Nat → Nat, OriginalListing g →
    ∃ (q : Nat) (hq : TotalBinary q), originalHeight g (policy q hq) = ⊤

end LogicLineages.ComputabilityKnowledge.PredictionOriginalHardnessTargets
