module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithmDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalComparator

def compareOutputs (a b : Nat) : Nat :=
  if a=0 then 0 else if b=0 then 1 else if a<b then 1 else 0

noncomputable def comparison (u v : Nat.Partrec.Code) (z : Nat) : Part Nat :=
  (PredictionOriginalMeasureAlgorithm.result u v z.unpair.1).bind fun a =>
    (PredictionOriginalMeasureAlgorithm.result u v z.unpair.2).map (compareOutputs a)

end LogicLineages.ComputabilityKnowledge.PredictionOriginalComparator
