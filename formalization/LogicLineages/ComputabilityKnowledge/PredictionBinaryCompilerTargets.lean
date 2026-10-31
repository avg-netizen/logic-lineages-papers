module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryCompilerDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryCompilerTargets
open Turing Turing.ToPartrec PredictionCompilerTapeSupport PredictionBinarySentinel PredictionBinaryCompiler

def ExactBinaryEvaluation : Prop :=
  ∀ (c : Code) (xs : List Bool) (b : Bool),
    [b.toNat] ∈ Code.eval c [inputNat xs] →
      final b ∈ StateTransition.eval (TM0.step (machine c)) (initial xs)

def ExactRawOutput : Prop :=
  ∀ (c : Code) (b : Bool), (final b).Tape.head = rawSymbol b ∧ TM0.step (machine c) (final b) = none

def ActualFiniteSupport : Prop :=
  ∀ c : Code, TM0.Supports (machine c) {l | l ∈ states c}

end LogicLineages.ComputabilityKnowledge.PredictionBinaryCompilerTargets
