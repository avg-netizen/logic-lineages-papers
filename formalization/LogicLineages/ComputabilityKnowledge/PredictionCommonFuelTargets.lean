module

public import LogicLineages.ComputabilityKnowledge.PredictionCommonFuelDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCommonFuelTargets
open PredictionGame PredictionLearning PredictionUniformHistory PredictionCommonFuel

def BooleanHistoriesExact : Prop :=
  ∀ (n : Nat) (xs : List Bool), xs ∈ booleanHistories n ↔ xs.length = n

def BooleanHistoriesPrimrec : Prop := Primrec booleanHistories

def CommonFuelTestExact : Prop :=
  ∀ (v : Code) (n s : Nat), commonFuelTest v n s = true ↔
    ∀ k : Nat, k ≤ n → ∀ xs : List Bool, xs.length = n →
      (boundedMove (compileSelfHistory v k) s xs).isSome = true

def CommonFuelTestPrimrec : Prop :=
  Primrec (fun x : Code × Nat × Nat => commonFuelTest x.1 x.2.1 x.2.2)

def CommonFuelEventuallySuccessful : Prop :=
  ∀ (v : Code), (∀ k : Nat, TotalBinary (compileSelfHistory v k)) →
    ∀ n : Nat, ∃ F : Nat, ∀ s : Nat, F ≤ s → commonFuelTest v n s = true

end LogicLineages.ComputabilityKnowledge.PredictionCommonFuelTargets
