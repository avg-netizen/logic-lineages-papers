module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundsDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapeHardnessTargets
@[expose] public section
/-! Source prop:hardness second clause for the source-stipulated original
listing requirements. The SAME total tape predictor family must handle
infinite extended-natural measure and every sufficiently high fixed level.
No numerical identity for an external AH evaluator is postulated or proved. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalHardness

def OriginalListing (g : Nat → Nat → Nat) : Prop :=
  Computable₂ g ∧ (∀ i : Nat, Primrec (g i)) ∧ PredictionOriginalBounds.CoversPR g

noncomputable def originalHeight (g : Nat → Nat → Nat) (p : PredictionGame.Policy) : WithTop Nat :=
  PredictionTapeMeasureContract.height (PredictionOriginalBounds.levelBound g) p

def MatrixTruth (R : PredictionFiniteChange.Matrix) (z : Nat) : Prop :=
  ∀ k : Nat, ∃ s : Nat, ∀ t : Nat, R (z, k, s, t) = true

end LogicLineages.ComputabilityKnowledge.PredictionOriginalHardness
