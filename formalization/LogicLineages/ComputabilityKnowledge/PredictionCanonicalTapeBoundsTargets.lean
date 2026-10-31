module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsTargets
open PredictionCanonicalTapeBounds

def ExactCanonicalCoverage : Prop := PredictionSourceFiniteValues.CoversComputable listing ∧
  ∀ i : Nat, Computable (listing i)

def ExactCanonicalBounds : Prop := ∀ m n,
  PredictionOriginalBounds.levelBound listing m n = PredictionMaximum.canonicalBound m n

def ActualSecondJumpBoundIndices : Prop := ∃ u : Nat.Partrec.Code,
  ComputableIn PredictionSecondJump.secondJumpOracles (positiveIndex u) ∧
  ∀ k : Nat,
    PredictionCanonicalList.TotalNat (Denumerable.ofNat Nat.Partrec.Code (positiveIndex u k)) ∧
    ∀ n, PredictionMaximum.evalValue (Denumerable.ofNat Nat.Partrec.Code (positiveIndex u k)) n =
      PredictionOriginalBounds.levelBound listing (k+1) n

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsTargets
