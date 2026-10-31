module
public import LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelDefinitions
@[expose] public section
/-! Literal terminal tape invariant for singleton binary outputs of the
actual source compiler. No output is inferred merely from termination. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayout
open Turing PredictionCompilerTapeSupport PredictionBinarySentinel

def outputTape (b : Bool) : Tape TapeAlphabet :=
  Tape.mk₁ (if b then [bottomSymbol, rawSymbol true] else [bottomSymbol])

def outputConfig (b : Bool) : TM1.Cfg TapeAlphabet TapeLabel Store :=
  ⟨none, none, outputTape b⟩

end LogicLineages.ComputabilityKnowledge.PredictionBinaryOutputLayout
