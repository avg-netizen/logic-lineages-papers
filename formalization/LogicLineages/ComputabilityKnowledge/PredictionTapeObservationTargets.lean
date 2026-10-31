module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeObservationDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeObservationTargets
open PredictionTapeObservation

def EffectiveObservation : Prop :=
  Primrec (fun z : Nat × Nat × List Bool => observe z.1 z.2.1 z.2.2) ∧
  Primrec (fun z : Nat × Nat × List Bool => boundedMove z.1 z.2.1 z.2.2)

def SoundObservation : Prop :=
  ∀ (code budget : Nat) (xs : List Bool) (v : Nat),
    observe code budget xs = some v → v ∈ naturalEval code xs

def ExactBinarySemantics : Prop :=
  ∀ (code : Nat) (xs : List Bool) (b : Bool),
    b ∈ PredictionUniformBinaryCompiler.binaryEval code xs ↔
      ∃ budget : Nat, boundedMove code budget xs = some b

def ObservationUniqueOnTotal : Prop :=
  ∀ (code : Nat) (h : TotalBinary code) (budget : Nat) (xs : List Bool) (v : Nat),
    observe code budget xs = some v → v = PredictionFiniteAlphabet.inputSymbol (policy code h xs)

end LogicLineages.ComputabilityKnowledge.PredictionTapeObservationTargets
