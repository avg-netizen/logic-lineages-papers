module

public import Mathlib.Computability.RecursiveIn

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleRelativeRecursion

def parameterRec (initial step : Nat → Nat) (input : Nat) : Nat :=
  Nat.rec (initial input.unpair.1)
    (fun j previous => step (Nat.pair input.unpair.1 (Nat.pair j previous))) input.unpair.2

def zeroSearch (test : Nat → Nat) (input : Nat) : Part Nat :=
  Nat.rfind fun candidate => Part.some (decide (test (Nat.pair input candidate) = 0))

end LogicLineages.ComputabilityKnowledge.OracleRelativeRecursion
