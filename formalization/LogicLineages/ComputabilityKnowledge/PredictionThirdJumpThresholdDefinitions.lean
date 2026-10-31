module
public import LogicLineages.ComputabilityKnowledge.PredictionSourceThresholdDefinitions
public import LogicLineages.ComputabilityKnowledge.OraclePiThreeDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThreshold

/-- Parameter=(predictor,bound-code), universal=(evader,membership witness),
existential=(counterexample,learning cutoff), last universal=certificate. -/
def packedMatrix (u : Nat.Partrec.Code) (z : Nat × Nat × Nat × Nat) : Bool :=
  PredictionSourceThreshold.thresholdMatrix u z.1.unpair.1
    (Denumerable.ofNat Nat.Partrec.Code z.1.unpair.2)
    z.2.1.unpair.1 z.2.1.unpair.2 z.2.2.1.unpair.1 z.2.2.1.unpair.2 z.2.2.2

noncomputable def decision (u : Nat.Partrec.Code) : Nat → Nat :=
  OraclePiThree.matrixIndicator (packedMatrix u)

end LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThreshold
