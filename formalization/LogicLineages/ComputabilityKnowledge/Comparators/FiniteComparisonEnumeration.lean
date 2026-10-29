module

public import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration

@[expose] public section

/-! Independent source-semantic counterexample-enumeration target for arbitrary
finite-depth Expr terms. Exact parser/syntax correspondence and surjective
finite positive tuple enumeration prevent an engineered numeric substitute. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.FiniteComparisonEnumeration

open PositiveExpression CircuitReduction
open LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration

def ExpressionDecoderExact : Prop :=
  ∀ (d : Nat) (xs : List Nat) (e : Expr Nat),
    decodeExpr d xs = some e ↔ xs = encodeExpr e ∧ Bounded d e

def PairDecoderExact : Prop :=
  ∀ (xs : List Nat) (d : Nat) (a b : Expr Nat),
    decodePair xs = some (d,a,b) ↔ xs = CircuitComparison.encodeComparison (d,a,b) ∧ Bounded d a ∧ Bounded d b

def EvaluationCorrect : Prop :=
  ∀ (d : Nat) (xs values : List Nat), evalCode d xs values =
    (decodeExpr d xs).map (fun e => e.eval (tupleValue values))

def FiniteEvaluationCorrect : Prop :=
  ∀ (d : Nat) (e : Expr Nat), Bounded d e → ∀ values : List Nat,
    evalCode d (encodeExpr e) values = some (e.eval (CircuitComparison.finiteVal (tupleOf d values)))

def TupleEnumerationSurjective : Prop :=
  ∀ (d : Nat) (ρ : Fin d → PosNat), ∃ k : Nat, enumTuple d k = ρ

def CounterexampleEnumeration : Prop :=
  (∀ xs : List Nat, StrictCounterexample xs ↔ ∃ k : Nat, checkStrict xs k = true) ∧
  (∀ xs : List Nat, WeakCounterexample xs ↔ ∃ k : Nat, checkWeak xs k = true)

def Target : Prop := ExpressionDecoderExact ∧ PairDecoderExact ∧ EvaluationCorrect ∧
  FiniteEvaluationCorrect ∧ TupleEnumerationSurjective ∧ CounterexampleEnumeration

end LogicLineages.ComputabilityKnowledge.Comparators.FiniteComparisonEnumeration
