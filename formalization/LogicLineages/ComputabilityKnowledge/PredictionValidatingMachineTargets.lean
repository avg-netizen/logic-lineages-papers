module
public import LogicLineages.ComputabilityKnowledge.PredictionValidatingMachineDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionValidatingMachineTargets
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionValidatingMachine

def ExactValidatorEvaluation : Prop :=
  ∀ t : Tape TapeAlphabet, StateTransition.eval (TM0.step machine) (initial t) =
    Part.ofOption ((PredictionNaturalOutputValidation.observe t).map (finish t))

def SourceBinarySemantics : Prop :=
  ∀ (n : Nat) (x : TM1.Cfg TapeAlphabet TapeLabel Store) (b : Bool),
    TM2to1.TrCfg (PartrecToTM2.halt [n]) x →
      (b ∈ (StateTransition.eval (TM0.step machine) (initial x.Tape)).map readout ↔ n = b.toNat)

def LoopDivergence : Prop :=
  ∀ t : Tape TapeAlphabet, StateTransition.eval (TM0.step machine) ⟨Label.loop, t⟩ = Part.none

end LogicLineages.ComputabilityKnowledge.PredictionValidatingMachineTargets
