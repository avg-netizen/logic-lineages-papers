module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeHardnessDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeHardnessTargets
open PredictionTapeObservation PredictionTapeRuntimeClass PredictionTapeHardness

def FixedBudgetHardness : Prop :=
  ∀ (R : PredictionFiniteChange.Matrix) (b : Nat → Nat), Computable R → Computable b →
    DominatesCodeEvaders b →
    ∃ f : Nat → Nat, Computable f ∧ ∃ hp : ∀ z : Nat, TotalBinary (f z),
      ∀ z : Nat, Threshold (policy (f z) (hp z)) b ↔
        ∀ k : Nat, ∃ s : Nat, ∀ t : Nat, R (z, k, s, t) = true

end LogicLineages.ComputabilityKnowledge.PredictionTapeHardnessTargets
