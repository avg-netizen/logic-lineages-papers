module
public import LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdTargets
open PredictionTapeObservation PredictionTapeRuntimeClass PredictionThirdJumpThreshold

def EffectivePackedMatrix : Prop := ∀ u : Nat.Partrec.Code, Primrec (packedMatrix u)

def ExactPackedFormula : Prop :=
  ∀ (u : Nat.Partrec.Code) (p : Nat) (bound : Nat.Partrec.Code),
    (∀ x : Nat, ∃ y : Nat, ∀ d : Nat, packedMatrix u (Nat.pair p (Encodable.encode bound), x, y, d) = true) ↔
      ∀ e a : Nat, ∃ b c : Nat, ∀ d : Nat, PredictionSourceThreshold.thresholdMatrix u p bound e a b c d = true

def UniformThirdJumpThreshold : Prop :=
  ∃ u : Nat.Partrec.Code,
    ComputableIn {fun n => Part.some (OraclePiThree.thirdJump n)} (decision u) ∧
    ∀ (p : Nat) (hp : TotalBinary p) (bound : Nat.Partrec.Code) (hf : PredictionCanonicalList.TotalNat bound),
      decision u (Nat.pair p (Encodable.encode bound)) = 1 ↔
        Threshold (policy p hp) (PredictionMaximum.evalValue bound)

end LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdTargets
