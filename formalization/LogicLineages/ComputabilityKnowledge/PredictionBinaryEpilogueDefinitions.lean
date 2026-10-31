module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayoutDefinitions
@[expose] public section
/-! A literal output epilogue: move right, write the observed binary value,
halt. Correctness requires the actual singleton compiler output invariant. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryEpilogue
open Turing PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
inductive Label | move | write | stop
instance : Inhabited Label := ⟨.move⟩

def machine : TM0.Machine TapeAlphabet Label := fun q a =>
  match q with
  | .move => some (.write, .move .right)
  | .write => some (.stop, .write (rawSymbol (workEq a (rawSymbol true))))
  | .stop => none

def initial (x : TM1.Cfg TapeAlphabet TapeLabel Store) : TM0.Cfg TapeAlphabet Label :=
  ⟨.move, x.Tape⟩

def final (b : Bool) (x : TM1.Cfg TapeAlphabet TapeLabel Store) : TM0.Cfg TapeAlphabet Label :=
  ⟨.stop, (x.Tape.move .right).write (rawSymbol b)⟩

/-- Fuel counts each ordinary successful transition and the halting observation. -/
def run : Nat → TM0.Cfg TapeAlphabet Label → Option (TM0.Cfg TapeAlphabet Label)
  | 0, _ => none
  | n + 1, x => match TM0.step machine x with
    | none => some x
    | some y => run n y

end LogicLineages.ComputabilityKnowledge.PredictionBinaryEpilogue
