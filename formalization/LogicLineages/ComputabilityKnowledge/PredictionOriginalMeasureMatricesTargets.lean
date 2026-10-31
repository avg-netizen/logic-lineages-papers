module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatricesDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatricesTargets
open PredictionOriginalMeasureMatrices PredictionTapeObservation PredictionTapeRuntimeClass

def EffectiveMatrices : Prop := ∀ u v : Nat.Partrec.Code,
  Primrec (levelMatrix u v) ∧ Primrec (infinityMatrix u v)

def ExactInfinityPacking : Prop := ∀ u v p,
  (∀ x, ∃ y, ∀ d, infinityMatrix u v (p,x,y,d) = true) ↔
    ∀ k, ∀ x, ∃ y, ∀ d, levelMatrix u v (Nat.pair p k,x,y,d) = true

def ActualOriginalDecisions : Prop :=
  ∀ g : Nat → Nat → Nat, Computable₂ g →
    ∃ u v : Nat.Partrec.Code,
      ComputableIn {fun n => Part.some (OraclePiThree.thirdJump n)} (levelDecision u v) ∧
      ComputableIn {fun n => Part.some (OraclePiThree.thirdJump n)} (infinityDecision u v) ∧
      ∀ (p : Nat) (hp : TotalBinary p),
        (∀ k, levelDecision u v (Nat.pair p k) = 1 ↔
          Threshold (policy p hp) (PredictionOriginalBounds.levelBound g (k+1))) ∧
        (infinityDecision u v p = 1 ↔ PredictionOriginalHardness.originalHeight g (policy p hp) = ⊤)

end LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatricesTargets
