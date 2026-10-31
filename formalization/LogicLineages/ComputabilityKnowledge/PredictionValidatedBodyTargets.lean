module
public import LogicLineages.ComputabilityKnowledge.PredictionValidatedBodyDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionValidatedBodyTargets
open Turing Turing.ToPartrec PredictionCompilerTapeSupport PredictionBinarySentinel PredictionValidatedBody

def FullBodyComposition : Prop :=
  ∀ x : TM0.Cfg TapeAlphabet PostLabel,
    StateTransition.eval (TM0.step machine) (sourceCfg x) =
      (StateTransition.eval (TM0.step postMachine) x).bind
        (fun terminal => (StateTransition.eval (TM0.step PredictionValidatingMachine.machine)
          (PredictionValidatingMachine.initial terminal.Tape)).map validatorCfg)

def ActualFiniteSupport : Prop :=
  ∀ c : Code, TM0.Supports machine {l | l ∈ states c}

def EntrySupported : Prop := ∀ (c : Code) (v : List Nat), (initial c v).q ∈ states c

def UniversalBinaryBody : Prop :=
  ∃ U : Code, ∀ (e : Nat) (xs : List Bool) (b : Bool),
    (b ∈ (StateTransition.eval (TM0.step machine) (initial U [inputNat xs, e])).map readout ↔
      b.toNat ∈ (Nat.Partrec.Code.ofNatCode e).eval (Encodable.encode xs))

end LogicLineages.ComputabilityKnowledge.PredictionValidatedBodyTargets
