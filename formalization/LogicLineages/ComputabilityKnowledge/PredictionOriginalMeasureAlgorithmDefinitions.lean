module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureMatricesDefinitions
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithm

noncomputable def searchTest (u v : Nat.Partrec.Code) (z : Nat) : Nat :=
  if PredictionOriginalMeasureMatrices.infinityDecision u v z.unpair.1 = 1 then 0
  else PredictionOriginalMeasureMatrices.levelDecision u v z

noncomputable def result (u v : Nat.Partrec.Code) (p : Nat) : Part Nat :=
  (OracleRelativeRecursion.zeroSearch (searchTest u v) p).map
    (fun k => if PredictionOriginalMeasureMatrices.infinityDecision u v p = 1 then 0 else k+1)

/-- Public output convention: zero denotes infinity; h+1 denotes finite h. -/
def outputValue (n : Nat) : WithTop Nat := if n=0 then ⊤ else ((n-1 : Nat) : WithTop Nat)

end LogicLineages.ComputabilityKnowledge.PredictionOriginalMeasureAlgorithm
