module
public import LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValuesDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionSecondJumpDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBounds

noncomputable def listing (i n : Nat) : Nat :=
  PredictionMaximum.evalValue (PredictionCanonicalList.canonicalCode i) n

noncomputable def height (p : PredictionGame.Policy) : WithTop Nat :=
  PredictionOriginalHardness.originalHeight listing p

noncomputable def positiveIndex (u : Nat.Partrec.Code) (k : Nat) : Nat :=
  PredictionSecondJump.compiledBoundIndex u (k+1)

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBounds
