module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryTableDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryTableTargets
open Turing Turing.ToPartrec PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality
open PredictionBinarySentinel PredictionBinaryTable

def ExactCodeDecoding : Prop :=
  ∀ c : Code, PredictionFiniteAlphabet.decodeTable (numericCode c) = numericTable c

def ExactSourceStep : Prop :=
  ∀ (c : Code) (x : TM0.Cfg TapeAlphabet Label), x.q ∈ PredictionBinaryCompiler.states c →
    PredictionCompilerFiniteExecution.tableStep (finiteData c) (numericCfg c x) =
      (TM0.step (PredictionBinaryCompiler.machine c) x).map (numericCfg c)

def ExactRawInitial : Prop :=
  ∀ (c : Code) (xs : List Bool),
    numericCfg c (PredictionBinaryCompiler.initial xs) = rawInitial workSymbols.length xs

def ExactRawEvaluation : Prop :=
  ∀ (c : Code) (xs : List Bool) (b : Bool), [b.toNat] ∈ Code.eval c [inputNat xs] →
    ∃ d, d ∈ numericEval c xs ∧ d.Tape.head.val = PredictionFiniteAlphabet.inputSymbol b

end LogicLineages.ComputabilityKnowledge.PredictionBinaryTableTargets
