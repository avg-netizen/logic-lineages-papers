module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrixDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionTapeLearningDefinitions
@[expose] public section
/-! Source paper14 prop:threshold / eq:pi3, using actual ordinary tape
runtime membership and actual simultaneous-game learning. The u parameter
is one fixed genuine reverse compiler, discharged in the final theorem.
Partial/nonbinary evaders cannot satisfy the membership antecedent. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionSourceThreshold

def thresholdMatrix (u : Nat.Partrec.Code) (p : Nat) (bound : Nat.Partrec.Code)
    (e a b c d : Nat) : Bool :=
  !(PredictionTapeMembershipMatrix.membershipMatrix e bound a b) ||
    PredictionTapeLearning.learningMatrix u p e c d

abbrev Data := Nat × Nat.Partrec.Code × Nat × Nat × Nat × Nat × Nat

end LogicLineages.ComputabilityKnowledge.PredictionSourceThreshold
