module

public import LogicLineages.ComputabilityKnowledge.PredictionTapeTableDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeTableTargets
open Turing PredictionTapeTable

def EffectiveDecoding : Prop :=
  Primrec decodeTable ∧ ∀ p : Table, decodeTable (Encodable.encode p) = p

def EffectiveBoundedSimulation : Prop :=
  Primrec (fun z : Nat × Nat × List Bool => simulate z.1 z.2.1 z.2.2)

def ExactSingleStep : Prop :=
  ∀ (p : Table) (c : Raw),
    (step p c).map toCfg = TM0.step (machine p) (toCfg c)

def ExactBoundedSimulation : Prop :=
  ∀ (p : Table) (fuel : Nat) (c d : Raw), bounded p fuel c = some d ↔
    ∃ n : Nat, n < fuel ∧ Run p c d n ∧ step p d = none

def ExactInitialTape : Prop :=
  ∀ (p : Table) (xs : List Bool),
    toCfg (initial p xs) = ⟨p.1, Tape.mk₁ (xs.map some)⟩

def MalformedCodeHalts : Prop :=
  ∀ code : Nat, Encodable.decode (α := Table) code = none → ∀ xs : List Bool,
    simulate code 1 xs = some (initial (0, []) xs)

end LogicLineages.ComputabilityKnowledge.PredictionTapeTableTargets
