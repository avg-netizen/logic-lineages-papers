module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeCodeDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeCodeTargets
open Turing PredictionTapeTable PredictionTapeCode

def EffectiveCodeFamily : Prop := Primrec code

def ExactCompiledStep : Prop :=
  ∀ (k : Nat) (c : PredictionTapeMachine.Cfg k),
    TM0.step (machine (table k)) (embedCfg k c) =
      (PredictionTapeMachine.step k c).map (embedCfg k)

def ExactCodedRuntime : Prop :=
  ∀ (k : Nat) (xs : List Bool) (fuel : Nat),
    (∃ d : Raw, simulate (code k) fuel xs = some d) ↔ min k xs.length + 2 ≤ fuel

def ExactCodedOutput : Prop :=
  ∀ (k : Nat) (xs : List Bool) (fuel : Nat) (d : Raw),
    simulate (code k) fuel xs = some d →
      d.1 = (if xs.length < k then k + 2 else k + 1) ∧
      d.2.1 = some (decide (xs.length < k))

def UniformConstantTime : Prop :=
  ∀ (k : Nat) (xs : List Bool), ∃ d : Raw,
    simulate (code k) (k + 2) xs = some d ∧ d.2.1 = some (decide (xs.length < k))

end LogicLineages.ComputabilityKnowledge.PredictionTapeCodeTargets
