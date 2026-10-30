module

public import LogicLineages.ComputabilityKnowledge.PredictionAvailabilityReductionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAvailabilityReductionTargets
open PredictionGame PredictionLearning PredictionFiniteChange PredictionCodeEvader PredictionFlipMask
open PredictionBaselineGame PredictionUniformHistory PredictionAvailabilityReduction

/-- Conditional reduction for the explicitly different evaln-availability
model. Both actual ordinary program families are constructed, not assumed. -/
def ConditionalOrdinaryAvailabilityReduction : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat), Computable R → Computable b →
    ∃ u v : Code, Computable (compileSelfHistory u) ∧ Computable (compileSelfHistory v) ∧
      ∃ hp : ∀ z : Nat, TotalBinary (compileSelfHistory u z),
      ∃ he : ∀ k : Nat, TotalBinary (compileSelfHistory v k),
        (∀ z : Nat, policy (compileSelfHistory u z) (hp z) = flipPolicy R b z) ∧
        (∀ k : Nat, policy (compileSelfHistory v k) (he k) = codePolicy k) ∧
        ((∀ k : Nat, UniformAvailable (compileSelfHistory v k) (he k) b) →
          ∀ z : Nat, LearnsAvailable b (policy (compileSelfHistory u z) (hp z)) ↔
            ∀ k : Nat, ∃ s : Nat, ∀ n : Nat, R (z, k, s, n) = true)

end LogicLineages.ComputabilityKnowledge.PredictionAvailabilityReductionTargets
