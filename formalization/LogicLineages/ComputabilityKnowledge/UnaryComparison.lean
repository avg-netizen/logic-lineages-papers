module

public import LogicLineages.ComputabilityKnowledge.ExponentialIdentity

@[expose] public section

/-! Literal unary universal-comparison procedure, paper02 thm:unary. Scan the
positive integers 1..T inclusively using the already explicit ray threshold.
Outer none means malformed input; inner none means universal success; inner
some n is the least positive counterexample. No asymptotic search is used. -/
namespace LogicLineages.ComputabilityKnowledge.UnaryComparison

open PositiveExpression RayFamilyClosure

def boundCode (pq : HeightCode × HeightCode) : Nat :=
  RaySeparation.threshold 1 [pq.1, pq.2]

def holdsAt (weak : Bool) (pq : HeightCode × HeightCode) (n : Nat) : Bool :=
  let a := RayCodeEvaluation.evalCode 1 pq.1.1 pq.1.2 [n]
  let b := RayCodeEvaluation.evalCode 1 pq.2.1 pq.2.2 [n]
  if weak then decide (a ≤ b) else decide (a < b)

def firstFailure (weak : Bool) (pq : HeightCode × HeightCode) (T : Nat) : Option Nat :=
  (List.range T).foldr (fun i acc => if holdsAt weak pq (i + 1) then acc else some (i + 1)) none

def resultCode (weak : Bool) (a b : List Nat) : Option (Option Nat) :=
  (ExponentialIdentity.normalInputs 1 a b).map (fun pq => firstFailure weak pq (boundCode pq))

def decisionCode (weak : Bool) (a b : List Nat) : Option Bool :=
  (resultCode weak a b).map Option.isNone

def Holds (weak : Bool) (a b : Expr (Fin 1)) (n : PosNat) : Prop :=
  if weak then a.eval (fun _ => n) ≤ b.eval (fun _ => n)
  else a.eval (fun _ => n) < b.eval (fun _ => n)

end LogicLineages.ComputabilityKnowledge.UnaryComparison
