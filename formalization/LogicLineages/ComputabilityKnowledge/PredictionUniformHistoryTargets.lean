module

public import LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryTargets
open PredictionGame PredictionLearning PredictionSelfHistory PredictionUniformHistory

def UniformReconstructionComputable : Prop :=
  ∀ R : ParameterRule, Computable (fun q : Nat × List Bool × List Bool => R q.1 q.2.1 q.2.2) →
    Computable (fun q : Nat × List Bool => reconstruct (R q.1) q.2)

def UniformSelfPolicyComputable : Prop :=
  ∀ R : ParameterRule, Computable (fun q : Nat × List Bool × List Bool => R q.1 q.2.1 q.2.2) →
    Computable (fun q : Nat × List Bool => selfPolicy (R q.1) q.2)

def UniformSelfHistoryProgram : Prop :=
  ∀ R : ParameterRule, Computable (fun q : Nat × List Bool × List Bool => R q.1 q.2.1 q.2.2) →
    ∃ u : Code, Computable (compileSelfHistory u) ∧
      (∀ z : Nat, ∀ xs : List Bool, Nat.Partrec.Code.eval u (Nat.pair z (Encodable.encode xs)) =
        Part.some (bitValue (selfPolicy (R z) xs))) ∧
      ∀ z : Nat, (∀ xs : List Bool, Nat.Partrec.Code.eval (compileSelfHistory u z) (Encodable.encode xs) =
        Part.some (bitValue (selfPolicy (R z) xs))) ∧
        ∃ hp : TotalBinary (compileSelfHistory u z), policy (compileSelfHistory u z) hp = selfPolicy (R z)

def UniformSelfHistoryPlay : Prop :=
  ∀ R : ParameterRule, Computable (fun q : Nat × List Bool × List Bool => R q.1 q.2.1 q.2.2) →
    ∃ u : Code, Computable (compileSelfHistory u) ∧ ∀ z : Nat,
      ∃ hp : TotalBinary (compileSelfHistory u z), ∀ (e : Policy) (n : Nat),
        let p := policy (compileSelfHistory u z) hp
        let h := histories p e n
        (h.evasions, h.predictions) = reconstruct (R z) h.evasions ∧
          prediction p e n = R z h.evasions h.predictions

end LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryTargets
