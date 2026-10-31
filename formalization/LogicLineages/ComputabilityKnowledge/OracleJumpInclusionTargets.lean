module

public import LogicLineages.ComputabilityKnowledge.OracleJumpInclusionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleJumpInclusionTargets
open OracleJumpInclusion OracleJump OraclePiThree

def LiftedSecondMatrixPrimitiveRecursive : Prop := Primrec liftedSecondMatrix

def ActualSecondIndicatorCalibration : Prop :=
  ∀ q, matrixIndicator liftedSecondMatrix q = secondJump q

def ActualSecondToThirdJumpInclusion : Prop :=
  ComputableIn {fun n => Part.some (thirdJump n)} secondJump

end LogicLineages.ComputabilityKnowledge.OracleJumpInclusionTargets
