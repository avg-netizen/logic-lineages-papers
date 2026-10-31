module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeObservationDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionRobustDefinitions
@[expose] public section
/-! Paper14 robust baseline using actual finite tape tables and strict ordinary
transition budgets, not Code.evaln. Timeouts are ignored historically;
halted nonbinary physical outputs fail comparison with the recorded bit. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeBaseline
open PredictionTapeObservation
open PredictionRobust (historyPrefix budgetPrefix)

def historicalTest (code : Nat) (budgets : List Nat) (xs ys : List Bool) (r : Nat) : Bool :=
  match observe code (budgets.getD r 0) (ys.take r) with
  | none => true
  | some v => decide (v = PredictionFiniteAlphabet.inputSymbol (xs.getD r false))

def eligible (budgets : List Nat) (xs ys : List Bool) (i : Nat) : Bool :=
  (List.range xs.length).all (historicalTest i budgets xs ys) &&
    (boundedMove i (budgets.getD xs.length 0) ys).isSome

def selectedIndex (budgets : List Nat) (xs ys : List Bool) : Nat :=
  (List.range (xs.length + 1)).findIdx (eligible budgets xs ys)

def indexedMove (budgets : List Nat) (xs ys : List Bool) (i : Nat) : Option Bool :=
  boundedMove i (budgets.getD xs.length 0) ys

def baseline (budgets : List Nat) (xs ys : List Bool) : Bool :=
  let i := selectedIndex budgets xs ys
  if i ≤ xs.length then (indexedMove budgets xs ys i).getD false else false

def available (e : Nat) (hp : TotalBinary e) (b : Nat → Nat) (y : Nat → Bool) : Prop :=
  ∃ N, ∀ n, N ≤ n →
    boundedMove e (b n) (historyPrefix y n) = some (policy e hp (historyPrefix y n))

end LogicLineages.ComputabilityKnowledge.PredictionTapeBaseline
