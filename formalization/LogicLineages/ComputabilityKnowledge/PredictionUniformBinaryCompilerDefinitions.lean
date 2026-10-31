module
public import LogicLineages.ComputabilityKnowledge.PredictionValidatedTableDefinitions
@[expose] public section
/-! Uniform numeric parameter insertion around a fixed finite validated body.
The evaluator uses the literal binary tape input and physical output symbols
1/2 (blank=0); a nonbinary terminal head has no binary result. No source
runtime or converse/acceptability assertion is built into this interface. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompiler
open Turing PredictionFiniteAlphabet

def readBit (n : Nat) : Option Bool :=
  if n = 1 then some false else if n = 2 then some true else none

def binaryEval (code : Nat) (xs : List Bool) : Part Bool :=
  let p := decodeTable code
  (StateTransition.eval (TM0.step (machine p)) (toCfg p (initial p xs))).bind
    (fun d => Part.ofOption (readBit d.Tape.head.val))

def compile (c : Turing.ToPartrec.Code) (e : Nat) : Nat :=
  PredictionNumericPrefixExecution.parameterCode (PredictionValidatedTable.numericTable c)
    (PredictionValidatedTable.bodyStates c) e

end LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompiler
