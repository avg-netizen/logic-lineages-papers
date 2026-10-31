module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteTableDefinitions
@[expose] public section
/-! Complete execution of the actual finite compiler on its encoded-stack
input. No rawbinary I/O adapter, time bound or numerical acceptability claim. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecution
open Turing Turing.ToPartrec Turing.PartrecToTM2
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality PredictionCompilerFiniteTable
open PredictionFiniteSerialization

def tableStep {q a : Nat} (m : FinMachine q a) :
    TM0.Cfg (Fin (a + 3)) Nat → Option (TM0.Cfg (Fin (a + 3)) Nat) :=
  TM0.step (PredictionFiniteAlphabet.machine (table 0 m))

def sourceInput (v : List Nat) : List TapeAlphabet := TM2to1.trInit K'.main (trList v)

def sourceInit (c : Code) (v : List Nat) : TM0.Cfg TapeAlphabet PostLabel :=
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  TM0.init (sourceInput v)

def compiledEval (c : Code) (v : List Nat) : Part (TM0.Cfg (Fin (workSymbols.length + 3)) Nat) :=
  StateTransition.eval (tableStep (finiteData c Cont'.halt))
    (numericCfg c Cont'.halt (sourceInit c v))

def outputRelated (c : Code) (w : List Nat)
    (d : TM0.Cfg (Fin (workSymbols.length + 3)) Nat) : Prop :=
  ∃ x : TM1.Cfg TapeAlphabet TapeLabel Store,
    TM2to1.TrCfg (PartrecToTM2.halt w) x ∧
    numericCfg c Cont'.halt (TM1to0.trCfg tapeMachine x) = d

end LogicLineages.ComputabilityKnowledge.PredictionCompilerFiniteExecution
