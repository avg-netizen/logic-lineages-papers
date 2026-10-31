module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutDefinitions
@[expose] public section
/-! Complete singleton-natural terminal layout and bounded binary validation.
Only head, next cell and following cell are inspected. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidation
open Turing PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
open PredictionBinaryParameterLayout

def value : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

def outputSymbols (n : Nat) : List TapeAlphabet := bottomSymbol :: (bits n).reverse.map rawSymbol

def outputConfig (n : Nat) : TM1.Cfg TapeAlphabet TapeLabel Store :=
  ⟨none, none, Tape.mk₁ (outputSymbols n)⟩

def recognize : List Bool → Option Bool
  | [] => some false
  | [true] => some true
  | _ => none

def observe (t : Tape TapeAlphabet) : Option Bool :=
  if workEq t.head bottomSymbol then
    if workEq (t.move .right).head default then some false
    else if workEq (t.move .right).head (rawSymbol true) &&
        workEq ((t.move .right).move .right).head default then some true else none
  else none

end LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidation
