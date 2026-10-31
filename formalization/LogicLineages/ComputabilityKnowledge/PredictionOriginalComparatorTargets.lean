module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalComparatorDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalComparatorTargets
open PredictionOriginalComparator PredictionOriginalHardness PredictionTapeObservation

def ExactOutputComparison : Prop := Primrec₂ compareOutputs ∧ ∀ a b,
  (compareOutputs a b = 0 ∨ compareOutputs a b = 1) ∧
  (compareOutputs a b = 1 ↔
    PredictionOriginalMeasureAlgorithm.outputValue a < PredictionOriginalMeasureAlgorithm.outputValue b)

def ActualComparatorUpper : Prop := ∀ g : Nat → Nat → Nat, Computable₂ g →
  ∃ u v : Nat.Partrec.Code,
    RecursiveIn {fun n => Part.some (OraclePiThree.thirdJump n)} (comparison u v) ∧
    ∀ (p q : Nat) (hp : TotalBinary p) (hq : TotalBinary q),
      ∃ bit : Nat, comparison u v (Nat.pair p q) = Part.some bit ∧
        (bit=0 ∨ bit=1) ∧
        (bit=1 ↔ originalHeight g (policy p hp) < originalHeight g (policy q hq))

def FixedInfiniteComparatorReduction : Prop := ∀ g : Nat → Nat → Nat, OriginalListing g →
  ∃ q : Nat, ∃ hq : TotalBinary q, originalHeight g (policy q hq) = ⊤ ∧
    ∀ R : Nat × Nat × Nat × Nat → Bool, Computable R →
      ∃ f : Nat → Nat, Computable f ∧ ∃ hp : ∀ z, TotalBinary (f z),
        ∀ z, (originalHeight g (policy (f z) (hp z)) < originalHeight g (policy q hq) ↔ ¬ MatrixTruth R z)

end LogicLineages.ComputabilityKnowledge.PredictionOriginalComparatorTargets
