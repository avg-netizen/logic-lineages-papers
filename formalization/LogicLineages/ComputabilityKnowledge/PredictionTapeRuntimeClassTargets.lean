module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassTargets
open PredictionTapeObservation PredictionTapeRuntime PredictionTapeRuntimeClass

def ExactAvailabilityCalibration : Prop :=
  ∀ (e : Nat) (he : TotalBinary e) (b : Nat → Nat),
    PredictionTapeGame.UniformAvailable e he b ↔ EventualRuntime e b

def EffectiveEvaderCodes : Prop := Primrec evaderCode

def ExactEvaderPolicy : Prop :=
  ∀ k : Nat, ∃ he : TotalBinary (evaderCode k),
    policy (evaderCode k) he = PredictionCodeEvader.codePolicy k

def ExactEvaderMembership : Prop :=
  ∀ (k : Nat) (b : Nat → Nat), EventualRuntime (evaderCode k) b ↔
    ∃ N, ∀ n, N ≤ n → min k n + 2 < b n

end LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassTargets
