module
public import LogicLineages.ComputabilityKnowledge.PredictionSourceThresholdDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSourceThresholdTargets
open PredictionTapeObservation PredictionTapeRuntimeClass PredictionSourceThreshold

def EffectiveThresholdMatrix : Prop :=
  ∀ u : Nat.Partrec.Code,
    Primrec (fun z : Data => thresholdMatrix u z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2)

def SourceThreshold : Prop :=
  ∃ u : Nat.Partrec.Code,
    Primrec (fun z : Data => thresholdMatrix u z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2) ∧
    ∀ (p : Nat) (hp : TotalBinary p) (bound : Nat.Partrec.Code) (hf : PredictionCanonicalList.TotalNat bound),
      Threshold (policy p hp) (PredictionMaximum.evalValue bound) ↔
        ∀ e a : Nat, ∃ b c : Nat, ∀ d : Nat, thresholdMatrix u p bound e a b c d = true

end LogicLineages.ComputabilityKnowledge.PredictionSourceThresholdTargets
