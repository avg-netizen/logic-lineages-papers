module

public import LogicLineages.ComputabilityKnowledge.PredictionCommonBudgetDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCommonBudgetTargets
open PredictionGame PredictionLearning PredictionUniformHistory PredictionCommonFuel
open PredictionCommonBudget PredictionBaselineGame

def CommonFuelSearchPartrec : Prop :=
  Partrec (fun x : Code × Nat => commonFuelSearch x.1 x.2)

def CommonFuelSearchTotal : Prop :=
  ∀ (v : Code), (∀ k : Nat, TotalBinary (compileSelfHistory v k)) →
    ∀ n : Nat, (commonFuelSearch v n).Dom

def ComputableSelectedFuel : Prop :=
  ∀ (v : Code), (∀ k : Nat, TotalBinary (compileSelfHistory v k)) →
    ∃ b : Nat → Nat, Computable b ∧ ∀ n : Nat, b n ∈ commonFuelSearch v n

def ActualCommonAvailableBudget : Prop :=
  ∀ (v : Code) (ht : ∀ k : Nat, TotalBinary (compileSelfHistory v k)),
    ∃ b : Nat → Nat, Computable b ∧
      ∀ k : Nat, UniformAvailable (compileSelfHistory v k) (ht k) b

end LogicLineages.ComputabilityKnowledge.PredictionCommonBudgetTargets
