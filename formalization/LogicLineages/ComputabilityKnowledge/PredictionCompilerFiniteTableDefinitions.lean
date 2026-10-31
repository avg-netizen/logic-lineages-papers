module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerPostEqualityProof
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationDefinitions
@[expose] public section
/-! Executable finite-table assembly of the actual sequential-code compiler.
This does not claim a uniform Computable map from ordinary natural indices.
Alphabet slots 1/2 are padding, NOT the source rawbinary input/output adapter. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTable
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality
open PredictionFiniteRenaming PredictionFiniteSerialization
local instance : DecidableEq TapeAlphabet := PredictionCompilerAlphabetEqualityProof.workDecidableEq
local instance : DecidableEq PostLabel := PredictionCompilerPostEqualityProof.postDecidableEq

def alphabetTail : List TapeAlphabet := default :: default :: workSymbols

def finitePost (c : Code) (k : Cont') :
    TM0.Machine (Fin (workSymbols.length + 3)) (Fin ((postLabels c k).length + 1)) :=
  letI : Inhabited Λ' := ⟨trNormal c k⟩
  renamed postMachine (postLabels c k) alphabetTail

def finiteCfg (c : Code) (k : Cont') (x : TM0.Cfg TapeAlphabet PostLabel) :
    TM0.Cfg (Fin (workSymbols.length + 3)) (Fin ((postLabels c k).length + 1)) :=
  letI : Inhabited Λ' := ⟨trNormal c k⟩
  x.map (toFinite alphabetTail) (toFinite (postLabels c k))

def action {a : Nat} : TM0.Stmt (Fin (a + 3)) → FinAction a
  | .move .left => .inl false
  | .move .right => .inl true
  | .write b => .inr b

def finiteData (c : Code) (k : Cont') : FinMachine (postLabels c k).length workSymbols.length :=
  fun q b => (finitePost c k q b).map (fun z => (z.1, action z.2))

def numericTable (c : Code) (k : Cont') : PredictionFiniteAlphabet.Table :=
  table 0 (finiteData c k)

def numericCode (c : Code) (k : Cont') : Nat := code 0 (finiteData c k)

def numericCfg (c : Code) (k : Cont') (x : TM0.Cfg TapeAlphabet PostLabel) :
    TM0.Cfg (Fin (workSymbols.length + 3)) Nat := embedCfg (finiteCfg c k x)

end LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTable
