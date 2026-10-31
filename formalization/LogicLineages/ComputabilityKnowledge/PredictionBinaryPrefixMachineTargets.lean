module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryPrefixMachineDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryPrefixMachineTargets
open Turing Turing.ToPartrec PredictionCompilerTapeSupport PredictionBinarySentinel PredictionBinaryPrefixMachine

def ExactFourTransitions : Prop :=
  ∀ (c : Code) (xs : List Bool), advance c 4 (initial xs) =
    some (embed (PredictionCompilerFiniteExecution.sourceInit c [inputNat xs]))

def ExactBodyStep : Prop :=
  ∀ (c : Code) (x : TM0.Cfg TapeAlphabet PostLabel),
    TM0.step (machine c) (embed x) = (TM0.step postMachine x).map embed

def PrefixTermination : Prop :=
  ∀ (c : Code) (xs : List Bool),
    (StateTransition.eval (TM0.step (machine c)) (initial xs)).Dom ↔
      (Code.eval c [inputNat xs]).Dom

end LogicLineages.ComputabilityKnowledge.PredictionBinaryPrefixMachineTargets
