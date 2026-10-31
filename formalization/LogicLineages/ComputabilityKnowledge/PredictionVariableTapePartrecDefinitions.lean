module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeObservationDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionLearning
@[expose] public section
/-! Reverse binary compiler for variable finite-alphabet tables. Uniformly
search the proved actual simulator for a physical bit, then return its 0/1
ordinary value. This translation does not preserve tape runtime. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrec

def observation (code fuel : Nat) (xs : List Bool) : Option Nat :=
  (PredictionTapeObservation.boundedMove code fuel xs).map Bool.toNat

def Produces (code : Nat) (xs : List Bool) (v : Nat) : Prop :=
  ∃ b : Bool, b ∈ PredictionUniformBinaryCompiler.binaryEval code xs ∧ v = b.toNat

def compile (universal : Nat.Partrec.Code) (code : Nat) : Nat.Partrec.Code :=
  Nat.Partrec.Code.curry universal code

end LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrec
