module

public import LogicLineages.ComputabilityKnowledge.AffineParameterComparison

@[expose] public section

/-! Complete affine one-parameter clause of paper02 cor:consumers, not its
WW vector or norm clauses. Actual original multivariable expressions are
compared under ai*n+bi with nonnegative coefficients and positive coordinates.
The least counterexample is the least positive parameter, not a tuple search. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.AffineParameterComparison

open PositiveExpression CircuitReduction
open LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration
open LogicLineages.ComputabilityKnowledge.AffineParameterSubstitution
open LogicLineages.ComputabilityKnowledge.AffineParameterComparison

def ExactValuation : Prop :=
  ∀ (d : Nat) (as bs : List Nat) (h : Admissible d as bs) (n : PosNat) (i : Fin d),
    (valuation d as bs h n i : Nat) = as.getD i.val 0 * (n : Nat) + bs.getD i.val 0

def ExactRawDomain : Prop :=
  ∀ (weak : Bool) (d : Nat) (as bs a b : List Nat),
    (resultCode weak d as bs a b).isSome =
      (coefficientsOK d as bs && ((decodeExpr d a).isSome && (decodeExpr d b).isSome)) ∧
    (decisionCode weak d as bs a b).isSome =
      (coefficientsOK d as bs && ((decodeExpr d a).isSome && (decodeExpr d b).isSome))

def SourceResult : Prop :=
  ∀ (weak : Bool) (d : Nat) (as bs : List Nat) (h : Admissible d as bs) (a b : Expr (Fin d)),
    (resultCode weak d as bs (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some none ↔ ∀ n : PosNat, Holds weak d as bs h a b n) ∧
    ∀ n, resultCode weak d as bs (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some (some n) ↔ ∃ hn : 0 < n, ¬Holds weak d as bs h a b ⟨n, hn⟩ ∧
        ∀ m : PosNat, (m : Nat) < n → Holds weak d as bs h a b m

def SourceDecision : Prop :=
  ∀ (weak : Bool) (d : Nat) (as bs : List Nat) (h : Admissible d as bs) (a b : Expr (Fin d)),
    (decisionCode weak d as bs (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some true ↔ ∀ n : PosNat, Holds weak d as bs h a b n) ∧
    (decisionCode weak d as bs (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some false ↔ ¬∀ n : PosNat, Holds weak d as bs h a b n)

def ActualUniformPrograms : Prop :=
  Primrec (fun p : Bool × Nat × List Nat × List Nat × List Nat × List Nat =>
    resultCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) ∧
  Primrec (fun p : Bool × Nat × List Nat × List Nat × List Nat × List Nat =>
    decisionCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

def Target : Prop := ExactValuation ∧ ExactRawDomain ∧ SourceResult ∧ SourceDecision ∧ ActualUniformPrograms

end LogicLineages.ComputabilityKnowledge.Comparators.AffineParameterComparison
