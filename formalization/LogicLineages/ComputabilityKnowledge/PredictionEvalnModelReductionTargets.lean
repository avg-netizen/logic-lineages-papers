module

public import LogicLineages.ComputabilityKnowledge.PredictionEvalnModelReductionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionEvalnModelReductionTargets
open PredictionGame PredictionLearning PredictionFiniteChange PredictionUniformHistory
open PredictionAvailabilityReduction

/-- An unconditional effective reduction in the explicitly named evaln model;
not the paper's runtime-based hardness theorem. -/
def ActualEvalnModelReduction : Prop :=
  ∀ (R : Matrix), Computable R →
    ∃ (b : Nat → Nat) (u : Code), Computable b ∧ Computable (compileSelfHistory u) ∧
      ∃ hp : ∀ z : Nat, TotalBinary (compileSelfHistory u z),
        ∀ z : Nat, LearnsAvailable b (policy (compileSelfHistory u z) (hp z)) ↔
          ∀ k : Nat, ∃ s : Nat, ∀ n : Nat, R (z, k, s, n) = true

end LogicLineages.ComputabilityKnowledge.PredictionEvalnModelReductionTargets
