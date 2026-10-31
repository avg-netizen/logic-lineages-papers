module
public import LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelDefinitions
@[expose] public section
/-! Exact constant left-prefix for source inputs [sentinel(xs), e].
The numeric word is primitive recursive and does not inspect the raw input. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayout
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality
open PredictionBinarySentinel

def bits : Nat → List Bool
  | n => if h : n = 0 then [] else decide (n % 2 = 1) :: bits (n / 2)
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def ordinaryCons : TapeAlphabet := (false, slots (some Γ'.cons) none none none)

def parameterWord (e : Nat) : List TapeAlphabet :=
  bottomSymbol :: ((bits e).reverse.map rawSymbol ++ [ordinaryCons, rawSymbol true])

local instance : DecidableEq TapeAlphabet := PredictionCompilerAlphabetEqualityProof.workDecidableEq

def symbolIndex (a : TapeAlphabet) : Nat := PredictionFiniteRenaming.index binaryAlphabetTail a

def numericWord (e : Nat) : List Nat :=
  symbolIndex bottomSymbol :: ((bits e).reverse.map PredictionFiniteAlphabet.inputSymbol ++
    [symbolIndex ordinaryCons, 2])

end LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayout
