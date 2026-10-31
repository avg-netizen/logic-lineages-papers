module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeTableDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionLearning
@[expose] public section
/-! The source-side semantics is actual finite tape execution ending in a
binary output, independent of the candidate's partial-recursive realization.
No time preservation through the translation is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapePartrec
open PredictionTapeTable PredictionLearning

def Produces (code : Nat) (xs : List Bool) (value : Nat) : Prop :=
  ∃ (n : Nat) (d : Raw) (b : Bool),
    Run (decodeTable code) (initial (decodeTable code) xs) d n ∧
    step (decodeTable code) d = none ∧ d.2.1 = some b ∧ value = bitValue b

def observation (code fuel : Nat) (xs : List Bool) : Option Nat :=
  (simulate code fuel xs).bind (fun d => d.2.1.map bitValue)

def compile (universal : Code) (code : Nat) : Code :=
  Nat.Partrec.Code.curry universal code

end LogicLineages.ComputabilityKnowledge.PredictionTapePartrec
