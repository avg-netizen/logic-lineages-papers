module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeLearningDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeLearningTargets
open PredictionTapeObservation PredictionTapeLearning

def EffectiveLearningMatrix : Prop :=
  ∀ u : Nat.Partrec.Code,
    Primrec (fun z : Nat × Nat × Nat × Nat => learningMatrix u z.1 z.2.1 z.2.2.1 z.2.2.2)

def SourceLearningMatrix : Prop :=
  ∃ u : Nat.Partrec.Code,
    Primrec (fun z : Nat × Nat × Nat × Nat => learningMatrix u z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
    ∀ (p e : Nat) (hp : TotalBinary p) (he : TotalBinary e),
      PredictionGame.Learns (policy p hp) (policy e he) ↔
        ∃ cutoff : Nat, ∀ certificate : Nat, learningMatrix u p e cutoff certificate = true

end LogicLineages.ComputabilityKnowledge.PredictionTapeLearningTargets
