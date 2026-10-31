module
public import LogicLineages.ComputabilityKnowledge.PredictionValidatedTableDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionValidatedTableTargets
open Turing Turing.ToPartrec PredictionCompilerTapeSupport PredictionBinarySentinel PredictionValidatedTable

def ExactCodeDecoding : Prop :=
  ∀ c : Code, PredictionFiniteAlphabet.decodeTable (numericCode c) = numericTable c

def BoundedNumericBody : Prop :=
  ∀ c : Code,
    (numericTable c).2.2.length = bodyStates c * PredictionFiniteAlphabet.width (numericTable c) ∧
    (numericTable c).2.1 < bodyStates c ∧
    TM0.Supports (PredictionFiniteAlphabet.machine (numericTable c)) {s | s < bodyStates c}

def FullNumericEvaluation : Prop :=
  ∀ (c : Code) (v : List Nat), numericEval c v =
    (StateTransition.eval (TM0.step PredictionValidatedBody.machine) (PredictionValidatedBody.initial c v)).map (numericCfg c)

def ExactPreparedInput : Prop :=
  ∀ (c : Code) (e : Nat) (xs : List Bool),
    numericCfg c (PredictionValidatedBody.initial c [inputNat xs, e]) = preparedInput c e xs

def UniversalNumericBody : Prop :=
  ∃ U : Code, ∀ (e : Nat) (xs : List Bool) (b : Bool),
    ((∃ d, d ∈ numericEval U [inputNat xs, e] ∧ d.Tape.head.val = PredictionFiniteAlphabet.inputSymbol b) ↔
      b.toNat ∈ (Nat.Partrec.Code.ofNatCode e).eval (Encodable.encode xs))

end LogicLineages.ComputabilityKnowledge.PredictionValidatedTableTargets
