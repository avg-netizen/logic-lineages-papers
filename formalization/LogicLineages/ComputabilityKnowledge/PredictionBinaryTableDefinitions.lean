module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryCompilerDefinitions
@[expose] public section
/-! Actual rawbinary finite-table numbering for the concrete compiler wrapper.
Alphabet 0 is blank and 1/2 are raw bits. The syntax→Nat constructor here is
not yet accompanied by a uniform Computable proof. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryTable
open Turing Turing.ToPartrec
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
open PredictionFiniteRenaming PredictionFiniteSerialization
local instance : DecidableEq PostLabel := PredictionCompilerPostEqualityProof.postDecidableEq
local instance : DecidableEq TapeAlphabet := PredictionCompilerAlphabetEqualityProof.workDecidableEq
deriving instance DecidableEq for PredictionBinaryCompiler.Label

abbrev Label := PredictionBinaryCompiler.Label

def finiteMachine (c : Code) :
    TM0.Machine (Fin (workSymbols.length + 3)) (Fin ((PredictionBinaryCompiler.states c).length + 1)) :=
  renamed (PredictionBinaryCompiler.machine c) (PredictionBinaryCompiler.states c) binaryAlphabetTail

def finiteCfg (c : Code) (x : TM0.Cfg TapeAlphabet Label) :
    TM0.Cfg (Fin (workSymbols.length + 3)) (Fin ((PredictionBinaryCompiler.states c).length + 1)) :=
  x.map (toFinite binaryAlphabetTail) (toFinite (PredictionBinaryCompiler.states c))

def finiteData (c : Code) : FinMachine (PredictionBinaryCompiler.states c).length workSymbols.length :=
  fun q b => (finiteMachine c q b).map (fun z => (z.1, PredictionCompilerFiniteTable.action z.2))

def numericTable (c : Code) : PredictionFiniteAlphabet.Table := table 0 (finiteData c)

def numericCode (c : Code) : Nat := code 0 (finiteData c)

def numericCfg (c : Code) (x : TM0.Cfg TapeAlphabet Label) :
    TM0.Cfg (Fin (workSymbols.length + 3)) Nat := embedCfg (finiteCfg c x)

def rawInitial (a : Nat) (xs : List Bool) : TM0.Cfg (Fin (a + 3)) Nat :=
  ⟨0, Tape.mk₁ (xs.map (fun b => ⟨PredictionFiniteAlphabet.inputSymbol b,
    by cases b <;> simp [PredictionFiniteAlphabet.inputSymbol] <;> omega⟩))⟩

def numericEval (c : Code) (xs : List Bool) : Part (TM0.Cfg (Fin (workSymbols.length + 3)) Nat) :=
  StateTransition.eval (PredictionCompilerFiniteExecution.tableStep (finiteData c))
    (rawInitial workSymbols.length xs)

end LogicLineages.ComputabilityKnowledge.PredictionBinaryTable
