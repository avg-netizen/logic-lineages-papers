module

public import LogicLineages.ComputabilityKnowledge.OracleRecursivePiThreeDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleRecursivePiThreeTargets
open OraclePiThree OracleRecursivePiThree PredictionLearning

def UniformObservationPrimrec : Prop :=
  Primrec (fun a : Nat.Partrec.Code × Nat × Nat × Nat × Nat => observationMatrix a.1 a.2) ∧
    Primrec codedObservation

def RecursiveMatrixCompiler : Prop :=
  ∀ R : Matrix, Computable R → ∃ code : Nat.Partrec.Code,
    ∀ a : Nat × Nat × Nat × Nat, code.eval (Encodable.encode a) = Part.some (bitValue (R a))

def UniversalObservationCalibration : Prop :=
  ∀ (R : Matrix) (code : Nat.Partrec.Code),
    (∀ a : Nat × Nat × Nat × Nat, code.eval (Encodable.encode a) = Part.some (bitValue (R a))) →
    ∀ i x y : Nat, (∀ w : Nat, observationMatrix code (i, x, y, w) = true) ↔
      ∀ z : Nat, R (i, x, y, z) = true

def UniformCodedThirdJumpDecision : Prop :=
  ComputableIn {fun n => Part.some (thirdJump n)} (matrixIndicator codedObservation)

def ActualRecursiveThirdJumpDecision : Prop :=
  ∀ R : Matrix, Computable R →
    ComputableIn {fun n => Part.some (thirdJump n)} (matrixIndicator R)

end LogicLineages.ComputabilityKnowledge.OracleRecursivePiThreeTargets
