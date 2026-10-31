module
public import LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundProgramsDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalHardnessDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatrices

def levelMatrix (u v : Nat.Partrec.Code) (z : Nat × Nat × Nat × Nat) : Bool :=
  PredictionThirdJumpThreshold.packedMatrix u
    (Nat.pair z.1.unpair.1 (Encodable.encode (PredictionOriginalBoundPrograms.compile v (z.1.unpair.2 + 1))),
      z.2.1, z.2.2.1, z.2.2.2)

def infinityMatrix (u v : Nat.Partrec.Code) (z : Nat × Nat × Nat × Nat) : Bool :=
  levelMatrix u v (Nat.pair z.1 z.2.1.unpair.1, z.2.1.unpair.2, z.2.2.1, z.2.2.2)

noncomputable def levelDecision (u v : Nat.Partrec.Code) : Nat → Nat :=
  OraclePiThree.matrixIndicator (levelMatrix u v)
noncomputable def infinityDecision (u v : Nat.Partrec.Code) : Nat → Nat :=
  OraclePiThree.matrixIndicator (infinityMatrix u v)

end LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatrices
