module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionThirdJumpThresholdDefinitions
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpper

noncomputable def selectedDecision (u v : Nat.Partrec.Code) (z : Nat) : Nat :=
  PredictionThirdJumpThreshold.decision u
    (Nat.pair z.unpair.1 (PredictionCanonicalTapeBounds.positiveIndex v z.unpair.2))

noncomputable def result (u v : Nat.Partrec.Code) (p : Nat) : Part Nat :=
  (OracleRelativeRecursion.zeroSearch (selectedDecision u v) p).map Nat.succ

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalMeasureUpper
