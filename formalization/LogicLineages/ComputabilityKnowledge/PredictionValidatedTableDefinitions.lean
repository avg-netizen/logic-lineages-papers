module
public import LogicLineages.ComputabilityKnowledge.PredictionValidatedBodyDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixExecutionDefinitions
@[expose] public section
/-! Finite numeric table of the validated body with explicit source entry.
No sentinel prefix is inserted: prepared input is the full [sentinel(xs),e]
stack tape. A later fixed-witness theorem uses this table as a constant. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionValidatedTable
open Turing Turing.ToPartrec
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionBinarySentinel
open PredictionFiniteRenaming PredictionFiniteSerialization
local instance : DecidableEq PostLabel := PredictionCompilerPostEqualityProof.postDecidableEq
local instance : DecidableEq TapeAlphabet := PredictionCompilerAlphabetEqualityProof.workDecidableEq
deriving instance DecidableEq for PredictionValidatingMachine.Label
deriving instance DecidableEq for PredictionValidatedBody.Label
abbrev Label := PredictionValidatedBody.Label

def finiteMachine (c : Code) :
    TM0.Machine (Fin (workSymbols.length + 3)) (Fin ((PredictionValidatedBody.states c).length + 1)) :=
  renamed PredictionValidatedBody.machine (PredictionValidatedBody.states c) binaryAlphabetTail

def finiteCfg (c : Code) (x : TM0.Cfg TapeAlphabet Label) :
    TM0.Cfg (Fin (workSymbols.length + 3)) (Fin ((PredictionValidatedBody.states c).length + 1)) :=
  x.map (toFinite binaryAlphabetTail) (toFinite (PredictionValidatedBody.states c))

def finiteData (c : Code) : FinMachine (PredictionValidatedBody.states c).length workSymbols.length :=
  fun q b => (finiteMachine c q b).map (fun z => (z.1, PredictionCompilerFiniteTable.action z.2))

def entry (c : Code) : Fin ((PredictionValidatedBody.states c).length + 1) :=
  encode (PredictionValidatedBody.states c) (PredictionValidatedBody.initial c []).q

def numericTable (c : Code) : PredictionFiniteAlphabet.Table := table (entry c) (finiteData c)
def numericCode (c : Code) : Nat := code (entry c) (finiteData c)
def bodyStates (c : Code) : Nat := (PredictionValidatedBody.states c).length + 1

def numericCfg (c : Code) (x : TM0.Cfg TapeAlphabet Label) :
    TM0.Cfg (Fin (workSymbols.length + 3)) Nat := embedCfg (finiteCfg c x)

def rawBits (a : Nat) (xs : List Bool) : List (Fin (a + 3)) :=
  xs.map (fun b => ⟨PredictionFiniteAlphabet.inputSymbol b,
    by cases b <;> simp [PredictionFiniteAlphabet.inputSymbol] <;> omega⟩)

def preparedAt {q a : Nat} (start : Fin (q + 1)) (m : FinMachine q a) (word : List Nat) (xs : List Bool) :
    TM0.Cfg (Fin (a + 3)) Nat :=
  PredictionNumericPrefixExecution.prepared (table start m) word (rawBits a xs)

def preparedInput (c : Code) (e : Nat) (xs : List Bool) : TM0.Cfg (Fin (workSymbols.length + 3)) Nat :=
  preparedAt (entry c) (finiteData c) (PredictionBinaryParameterLayout.numericWord e) xs

def numericEval (c : Code) (v : List Nat) : Part (TM0.Cfg (Fin (workSymbols.length + 3)) Nat) :=
  StateTransition.eval (PredictionCompilerFiniteExecution.tableStep (finiteData c))
    (numericCfg c (PredictionValidatedBody.initial c v))

end LogicLineages.ComputabilityKnowledge.PredictionValidatedTable
