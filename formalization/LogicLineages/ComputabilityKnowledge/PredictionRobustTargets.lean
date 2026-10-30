module

public import LogicLineages.ComputabilityKnowledge.PredictionRobustDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRobustTargets
open PredictionLearning PredictionRobust

def LeastEligibleSelection : Prop :=
  ∀ (budgets : List Nat) (xs ys : List Bool) (k : Nat),
    k ≤ xs.length → eligible budgets xs ys k = true →
      selectedIndex budgets xs ys ≤ k ∧
      eligible budgets xs ys (selectedIndex budgets xs ys) = true

/-- A real selected candidate, never the sentinel fallback, is permanently
excluded after its wrong output. The historical budget is fixed at b(n). -/
def WrongSelectionExcluded : Prop :=
  ∀ (b : Nat → Nat) (x y : Nat → Bool) (n m : Nat), n < m →
    let i := selectedIndex (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n)
    i ≤ n → eligible (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) i = true →
    baseline (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) ≠ x n →
    eligible (budgetPrefix b m) (historyPrefix x m) (historyPrefix y m) i = false

def TrueProgramEventuallyEligible : Prop :=
  ∀ (e : Code) (hp : TotalBinary e) (b : Nat → Nat) (y : Nat → Bool),
    available e hp b y →
    let x := fun n => policy e hp (historyPrefix y n)
    ∃ N, ∀ n, N ≤ n → Encodable.encode e ≤ n ∧
      eligible (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) (Encodable.encode e) = true

def RobustBoundedObservations : Prop :=
  ∀ (e : Code) (hp : TotalBinary e) (b : Nat → Nat) (y : Nat → Bool),
    available e hp b y →
    let x := fun n => policy e hp (historyPrefix y n)
    ∃ N, ∀ n, N ≤ n →
      baseline (budgetPrefix b n) (historyPrefix x n) (historyPrefix y n) = x n

def PrimitiveRecursiveBaseline : Prop :=
  Primrec (fun h : List Nat × List Bool × List Bool => baseline h.1 h.2.1 h.2.2)

end LogicLineages.ComputabilityKnowledge.PredictionRobustTargets
