module
public import LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidationDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidationTargets
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionBinaryParameterLayout
open PredictionNaturalOutputValidation

def ExactBitValue : Prop := ∀ n : Nat, value (bits n) = n

def ExactSourceTape : Prop :=
  ∀ n : Nat, PredictionCompilerFiniteExecution.sourceInput [n] = outputSymbols n

def ExactSingletonLayout : Prop :=
  ∀ (n : Nat) (x : TM1.Cfg TapeAlphabet TapeLabel Store),
    TM2to1.TrCfg (PartrecToTM2.halt [n]) x ↔ x = outputConfig n

def ExactBoundedObservation : Prop :=
  ∀ (n : Nat) (x : TM1.Cfg TapeAlphabet TapeLabel Store) (b : Bool),
    TM2to1.TrCfg (PartrecToTM2.halt [n]) x → (observe x.Tape = some b ↔ n = b.toNat)

end LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidationTargets
