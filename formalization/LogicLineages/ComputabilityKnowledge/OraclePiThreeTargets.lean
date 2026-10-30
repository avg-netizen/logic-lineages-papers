module

public import LogicLineages.ComputabilityKnowledge.OraclePiThreeDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OraclePiThreeTargets
open OracleJump OraclePiThree

def CounterMatrixCalibration : Prop :=
  ∀ R : Matrix, Primrec R → Primrec (counterMatrix R) ∧
    ∀ i x : Nat, counterIndicator R (Nat.pair i x) = 1 ↔
      ∀ y : Nat, ∃ z : Nat, R (i, x, y, z) = false

def RelativePiThreeCounterSearch : Prop :=
  ∀ R : Matrix, Primrec R →
    RecursiveIn {fun n => Part.some (secondJump n)} (counterSearch R)

def ExactPiThreeCounterDomain : Prop :=
  ∀ (R : Matrix) (i : Nat), (counterSearch R i).Dom ↔
    ∃ x : Nat, ∀ y : Nat, ∃ z : Nat, R (i, x, y, z) = false

def ActualPiThreeThirdJumpDecision : Prop :=
  ∀ R : Matrix, Primrec R →
    ComputableIn {fun n => Part.some (thirdJump n)} (matrixIndicator R)

end LogicLineages.ComputabilityKnowledge.OraclePiThreeTargets
