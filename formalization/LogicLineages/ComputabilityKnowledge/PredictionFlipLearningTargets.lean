module

public import LogicLineages.ComputabilityKnowledge.PredictionFlipLearningDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFlipLearningTargets
open PredictionGame PredictionLearning PredictionFiniteChange PredictionCodeEvader PredictionFlipMask
open PredictionBaselineGame PredictionUniformHistory

def ActualFlipPolicyCalibration : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat) (z : Nat) (e : Policy) (n : Nat),
    let p := flipPolicy R b z
    let h := histories p e n
    prediction p e n = if flipEvent R z h.evasions then !(budgetRule b h.evasions h.predictions)
      else budgetRule b h.evasions h.predictions

def UniformFlipPolicyProgram : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat), Computable R → Computable b →
    ∃ u : Code, Computable (compileSelfHistory u) ∧ ∀ z : Nat,
      ∃ hp : TotalBinary (compileSelfHistory u z), policy (compileSelfHistory u z) hp = flipPolicy R b z

def PositiveFlipLearning : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat) (z : Nat), (∀ k : Nat, (changeSet R z k).Finite) →
    ∀ (e : Code) (he : TotalBinary e), UniformAvailable e he b → Learns (flipPolicy R b z) (policy e he)

def NegativeFlipLearning : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat) (z k : Nat), (changeSet R z k).Infinite →
    ∀ (e : Code) (he : TotalBinary e), policy e he = codePolicy k → UniformAvailable e he b →
      ¬ Learns (flipPolicy R b z) (policy e he)

end LogicLineages.ComputabilityKnowledge.PredictionFlipLearningTargets
