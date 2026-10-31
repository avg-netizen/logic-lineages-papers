module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeBaselineDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeBaselineTargets
open PredictionTapeObservation PredictionTapeBaseline
open PredictionRobust (historyPrefix budgetPrefix)

def LeastEligibleSelection : Prop :=
  ∀ (budgets : List Nat) (xs ys : List Bool) (k : Nat),
    k ≤ xs.length → eligible budgets xs ys k = true →
      selectedIndex budgets xs ys ≤ k ∧
      eligible budgets xs ys (selectedIndex budgets xs ys) = true

def WrongSelectionExcluded : Prop :=
  ∀ (b : Nat → Nat) (x y : Nat → Bool) (n m : Nat), n < m →
    let i := selectedIndex (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n)
    i ≤ n → eligible (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) i = true →
    baseline (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) ≠ x n →
    eligible (budgetPrefix b m) (historyPrefix x m) (historyPrefix y m) i = false

def TrueProgramEventuallyEligible : Prop :=
  ∀ (e : Nat) (hp : TotalBinary e) (b : Nat → Nat) (y : Nat → Bool),
    available e hp b y →
    let x := fun n => policy e hp (historyPrefix y n)
    ∃ N, ∀ n, N ≤ n → e ≤ n ∧
      eligible (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) e = true

def RobustBoundedObservations : Prop :=
  ∀ (e : Nat) (hp : TotalBinary e) (b : Nat → Nat) (y : Nat → Bool),
    available e hp b y →
    let x := fun n => policy e hp (historyPrefix y n)
    ∃ N, ∀ n, N ≤ n → baseline (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) = x n

def PrimitiveRecursiveBaseline : Prop :=
  Primrec (fun h : List Nat × List Bool × List Bool => baseline h.1 h.2.1 h.2.2)

end LogicLineages.ComputabilityKnowledge.PredictionTapeBaselineTargets
