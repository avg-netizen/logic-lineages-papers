module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecisionDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecisionTargets
open NormalForm SingleNamePlainDecision

def ValuationIndependence : Prop := ∀ (i : Nat) (p : Formula), SingleNamePlain.admissible i p = true →
  ∀ ν μ : Nat → Nat,
    ((∃ n : Nat, p.eval (Function.update ν i n)) ↔ ∃ n : Nat, p.eval (Function.update μ i n)) ∧
    ((∀ n : Nat, p.eval (Function.update ν i n)) ↔ ∀ n : Nat, p.eval (Function.update μ i n))

def ExactDecisionDomain : Prop := ∀ (i : Nat) (p : Formula),
  (existsDecision i p).isSome = SingleNamePlain.admissible i p ∧
  (forallDecision i p).isSome = SingleNamePlain.admissible i p

def ActualExistentialDecision : Prop := ∀ (i : Nat) (p : Formula), SingleNamePlain.admissible i p = true →
  ∀ (ν : Nat → Nat) (answer : Bool), existsDecision i p = some answer ↔
    ((∃ n : Nat, p.eval (Function.update ν i n)) ↔ answer = true)

def ActualUniversalDecision : Prop := ∀ (i : Nat) (p : Formula), SingleNamePlain.admissible i p = true →
  ∀ (ν : Nat → Nat) (answer : Bool), forallDecision i p = some answer ↔
    ((∀ n : Nat, p.eval (Function.update ν i n)) ↔ answer = true)

def LiteralCodeCalibration : Prop := ∀ (i : Nat) (p : Formula),
  Code.existsDecision i p.encode = existsDecision i p ∧
  Code.forallDecision i p.encode = forallDecision i p

def ActualNumericPrograms : Prop := Primrec₂ Code.existsDecision ∧ Primrec₂ Code.forallDecision

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecisionTargets
