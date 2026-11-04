module
public import LogicLineages.OrdinalComparison.SourceBlankHaltingReductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Targets
open Turing LogicLineages.ComputabilityKnowledge
open PredictionFiniteAlphabet

def ExactNormalization : Prop :=
  Primrec normalize ∧ Primrec normalizedIndex ∧
  ∀ (c : Nat.Partrec.Code) (x : Nat),
    (normalize c).eval x = (fun _ : Nat => 0) <$> c.eval 0

def ValidatedTerminalBridge : Prop :=
  ∀ (U : Turing.ToPartrec.Code) (e : Nat) (xs : List Bool),
    (∀ d, d ∈ machineEval (PredictionUniformBinaryCompiler.compile U e) xs →
      ∃ b : Bool, d.Tape.head.val = inputSymbol b) ∧
    ((machineEval (PredictionUniformBinaryCompiler.compile U e) xs).Dom ↔
      (PredictionUniformBinaryCompiler.binaryEval
        (PredictionUniformBinaryCompiler.compile U e) xs).Dom)

def EffectiveBlankReduction : Prop :=
  ∃ U : Turing.ToPartrec.Code, Primrec (translate U) ∧
    ∀ c : Nat.Partrec.Code,
      SourceBlankMachineSimulation.Halts (translate U (Encodable.encode c)) ↔
        (c.eval 0).Dom

def BlankHaltingUndecidable : Prop :=
  ¬ ComputablePred SourceBlankMachineSimulation.Halts
end LogicLineages.OrdinalComparison.SourceBlankHaltingReduction.Targets
