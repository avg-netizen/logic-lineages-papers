module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecutionDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
/-! Raw binary input layout for the actual stack compiler. Leading sentinel
one preserves length/leading zeros. The two prepended cells are an exact
layout fact here, not an assumed machine execution or runtime bound. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionBinarySentinel
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality

def bitSymbol (b : Bool) : Γ' := if b then .bit1 else .bit0

def inputNat (xs : List Bool) : Nat := xs.foldl (fun n b => 2 * n + b.toNat) 1

def rawSymbol (b : Bool) : TapeAlphabet := (false, slots (some (bitSymbol b)) none none none)

def bottomSymbol : TapeAlphabet := (true, slots (some Γ'.cons) none none none)

def binaryAlphabetTail : List TapeAlphabet := rawSymbol false :: rawSymbol true :: workSymbols

local instance : DecidableEq TapeAlphabet := PredictionCompilerAlphabetEqualityProof.workDecidableEq

def rawIndex (b : Bool) : Nat := PredictionFiniteRenaming.index binaryAlphabetTail (rawSymbol b)

end LogicLineages.ComputabilityKnowledge.PredictionBinarySentinel
