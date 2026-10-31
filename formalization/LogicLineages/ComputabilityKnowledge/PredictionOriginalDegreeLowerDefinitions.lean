module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalComparatorDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLower
open PredictionTapeObservation PredictionOriginalHardness

/-- Total oracle extensions are constrained only on promised total predictors. -/
def MeasureOracle (g : Nat → Nat → Nat) (A : Nat → Nat) : Prop :=
  ∀ p (hp : TotalBinary p), PredictionOriginalMeasureAlgorithm.outputValue (A p) = originalHeight g (policy p hp)

def ComparatorOracle (g : Nat → Nat → Nat) (A : Nat → Nat) : Prop :=
  ∀ p q (hp : TotalBinary p) (hq : TotalBinary q),
    (A (Nat.pair p q)=0 ∨ A (Nat.pair p q)=1) ∧
    (A (Nat.pair p q)=1 ↔ originalHeight g (policy p hp) < originalHeight g (policy q hq))

end LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLower
