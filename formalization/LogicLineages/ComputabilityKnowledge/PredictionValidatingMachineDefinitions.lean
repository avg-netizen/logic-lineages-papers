module
public import LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidationDefinitions
@[expose] public section
/-! Actual finite-state validator. Invalid outputs enter a literal self-loop;
valid outputs write raw 0/1 under the terminal head. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionValidatingMachine
open Turing PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
inductive Label | check | first | second | stop | loop
instance : Inhabited Label := ⟨.check⟩

def machine : TM0.Machine TapeAlphabet Label := fun q a =>
  match q with
  | .check => if workEq a bottomSymbol then some (.first, .move .right)
      else some (.loop, .write a)
  | .first => if workEq a default then some (.stop, .write (rawSymbol false))
      else if workEq a (rawSymbol true) then some (.second, .move .right)
      else some (.loop, .write a)
  | .second => if workEq a default then some (.stop, .write (rawSymbol true))
      else some (.loop, .write a)
  | .stop => none
  | .loop => some (.loop, .write a)

def initial (t : Tape TapeAlphabet) : TM0.Cfg TapeAlphabet Label := ⟨.check, t⟩

def finish (t : Tape TapeAlphabet) (b : Bool) : TM0.Cfg TapeAlphabet Label :=
  ⟨.stop, (if b then (t.move .right).move .right else t.move .right).write (rawSymbol b)⟩

def readout (d : TM0.Cfg TapeAlphabet Label) : Bool := workEq d.Tape.head (rawSymbol true)

end LogicLineages.ComputabilityKnowledge.PredictionValidatingMachine
