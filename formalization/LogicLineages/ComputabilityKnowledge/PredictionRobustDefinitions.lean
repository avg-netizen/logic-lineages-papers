module

public import LogicLineages.ComputabilityKnowledge.PredictionLearning

@[expose] public section

/-! Paper 14, lines 227–259: finite least-eligible search on actual paired
histories. These observations use `Code.evaln` fuel, NOT source tape runtime.
The runtime-to-observation bridge remains separate and unproved. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionRobust
open PredictionLearning

def historyPrefix {α : Type} (s : Nat → α) (n : Nat) : List α :=
  List.ofFn (fun i : Fin n => s i)

def budgetPrefix (b : Nat → Nat) (n : Nat) : List Nat := historyPrefix b (n + 1)

/-- Timeout is ignored; every halted raw value, including nonbinary values,
is compared to the recorded evasion bit. -/
def historicalTest (c : Code) (budgets : List Nat) (xs ys : List Bool)
    (r : Nat) : Bool :=
  match Nat.Partrec.Code.evaln (budgets.getD r 0) c (Encodable.encode (ys.take r)) with
  | none => true
  | some v => decide (v = bitValue (xs.getD r false))

def eligible (budgets : List Nat) (xs ys : List Bool) (i : Nat) : Bool :=
  match Encodable.decode (α := Code) i with
  | none => false
  | some c =>
      (List.range xs.length).all (historicalTest c budgets xs ys) &&
        (boundedMove c (budgets.getD xs.length 0) ys).isSome

/-- On the range list the position equals the program index; failure returns
`xs.length + 1`, outside the finite search. -/
def selectedIndex (budgets : List Nat) (xs ys : List Bool) : Nat :=
  (List.range (xs.length + 1)).findIdx (eligible budgets xs ys)

def indexedMove (budgets : List Nat) (xs ys : List Bool) (i : Nat) : Option Bool :=
  (Encodable.decode (α := Code) i).bind
    (fun c => boundedMove c (budgets.getD xs.length 0) ys)

def baseline (budgets : List Nat) (xs ys : List Bool) : Bool :=
  let i := selectedIndex budgets xs ys
  if i ≤ xs.length then (indexedMove budgets xs ys i).getD false else false

def available (e : Code) (hp : TotalBinary e) (b : Nat → Nat)
    (y : Nat → Bool) : Prop :=
  ∃ N, ∀ n, N ≤ n →
    boundedMove e (b n) (historyPrefix y n) = some (policy e hp (historyPrefix y n))

end LogicLineages.ComputabilityKnowledge.PredictionRobust
