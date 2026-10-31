module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalDegreeLowerDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalClassification
open PredictionTapeObservation PredictionOriginalHardness PredictionOriginalDegreeLower

/-- Recursive Pi3 definition and reductions whose entire image is in the promise. -/
def CompletePiThreeOnTotal (P : (p : Nat) → TotalBinary p → Prop) : Prop :=
  (∃ M : OraclePiThree.Matrix, Primrec M ∧ ∀ p (hp : TotalBinary p),
    (P p hp ↔ ∀ x, ∃ y, ∀ z, M (p,x,y,z)=true)) ∧
  (∀ R : OraclePiThree.Matrix, Computable R →
    ∃ f : Nat → Nat, Computable f ∧ ∃ hp : ∀ z, TotalBinary (f z),
      ∀ z, (P (f z) (hp z) ↔ MatrixTruth R z))

def MeasureDegree (g : Nat → Nat → Nat) : Prop :=
  (∃ M : Nat → Part Nat, RecursiveIn {fun n => Part.some (OraclePiThree.thirdJump n)} M ∧
    ∀ p (hp : TotalBinary p), ∃ output, M p=Part.some output ∧
      PredictionOriginalMeasureAlgorithm.outputValue output = originalHeight g (policy p hp)) ∧
  (∀ A : Nat → Nat, MeasureOracle g A →
    ComputableIn {fun n => Part.some (A n)} OraclePiThree.thirdJump)

def ComparatorDegree (g : Nat → Nat → Nat) : Prop :=
  (∃ M : Nat → Part Nat, RecursiveIn {fun n => Part.some (OraclePiThree.thirdJump n)} M ∧
    ∀ p q (hp : TotalBinary p) (hq : TotalBinary q), ∃ bit,
      M (Nat.pair p q)=Part.some bit ∧ (bit=0 ∨ bit=1) ∧
      (bit=1 ↔ originalHeight g (policy p hp) < originalHeight g (policy q hq))) ∧
  (∀ A : Nat → Nat, ComparatorOracle g A →
    ComputableIn {fun n => Part.some (A n)} OraclePiThree.thirdJump)

end LogicLineages.ComputabilityKnowledge.PredictionOriginalClassification
