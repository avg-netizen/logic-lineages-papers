module

public import LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryTargets
open PredictionGame PredictionLearning PredictionSelfHistory

def ReconstructionLengths : Prop :=
  ∀ (R : PairedRule) (xs : List Bool),
    (reconstruct R xs).1 = xs ∧ (reconstruct R xs).2.length = xs.length

def ReconstructionAppend : Prop :=
  ∀ (R : PairedRule) (xs : List Bool) (x : Bool),
    reconstruct R (xs ++ [x]) = (xs ++ [x], (reconstruct R xs).2 ++ [selfPolicy R xs])

def ActualHistoryCalibration : Prop :=
  ∀ (R : PairedRule) (evader : Policy) (n : Nat),
    let h := histories (selfPolicy R) evader n
    (h.evasions, h.predictions) = reconstruct R h.evasions ∧
      prediction (selfPolicy R) evader n = R h.evasions h.predictions

def PrimitiveRecursiveSelfPolicy : Prop :=
  ∀ (R : PairedRule), Primrec₂ R → Primrec (selfPolicy R)

def OrdinarySelfPolicyProgram : Prop :=
  ∀ (R : PairedRule), Primrec₂ R →
    ∃ (p : Code) (hp : TotalBinary p), policy p hp = selfPolicy R

end LogicLineages.ComputabilityKnowledge.PredictionSelfHistoryTargets
