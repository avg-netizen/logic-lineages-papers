module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeFlipDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeFlipTargets
open PredictionGame PredictionFiniteChange PredictionTapeObservation PredictionTapeGame PredictionTapeFlip

def ComputableFlipRule : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat), Computable R → Computable b →
    Computable (fun q : Nat × List Bool × List Bool => flipRule R b q.1 q.2.1 q.2.2)

def UniformTapeFlipProgram : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat), Computable R → Computable b →
    ∃ g : Nat → Nat, Computable g ∧ ∀ z : Nat,
      ∃ hp : TotalBinary (g z), policy (g z) hp = flipPolicy R b z

def PositiveTapeFlipLearning : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat) (z : Nat), (∀ k : Nat, (changeSet R z k).Finite) →
    ∀ (e : Nat) (he : TotalBinary e), UniformAvailable e he b → Learns (flipPolicy R b z) (policy e he)

def NegativeTapeFlipLearning : Prop :=
  ∀ (R : Matrix) (b : Nat → Nat) (z k : Nat), (changeSet R z k).Infinite →
    ∀ (e : Nat) (he : TotalBinary e), policy e he = PredictionCodeEvader.codePolicy k →
      UniformAvailable e he b → ¬ Learns (flipPolicy R b z) (policy e he)

end LogicLineages.ComputabilityKnowledge.PredictionTapeFlipTargets
