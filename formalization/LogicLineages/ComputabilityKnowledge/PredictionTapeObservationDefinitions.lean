module
public import LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompilerDefinitions
@[expose] public section
/-! Literal ordinary-tape observations for paper14's strict time budget.
Fuel counts the terminal halt observation, so testing time < budget uses
fuel budget-1. Historical observations retain nonbinary physical symbols. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeObservation
open Turing PredictionFiniteAlphabet

def naturalEval (code : Nat) (xs : List Bool) : Part Nat :=
  let p := decodeTable code
  (StateTransition.eval (TM0.step (machine p)) (toCfg p (initial p xs))).map
    (fun d => d.Tape.head.val)

def observe (code budget : Nat) (xs : List Bool) : Option Nat :=
  (simulate code (budget - 1) xs).map (fun d => d.2.1 % width (decodeTable code))

def boundedMove (code budget : Nat) (xs : List Bool) : Option Bool :=
  (observe code budget xs).bind PredictionUniformBinaryCompiler.readBit

def TotalBinary (code : Nat) : Prop :=
  ∀ xs : List Bool, ∃ b : Bool, b ∈ PredictionUniformBinaryCompiler.binaryEval code xs

noncomputable def policy (code : Nat) (h : TotalBinary code) : List Bool → Bool :=
  fun xs => Classical.choose (h xs)

end LogicLineages.ComputabilityKnowledge.PredictionTapeObservation
