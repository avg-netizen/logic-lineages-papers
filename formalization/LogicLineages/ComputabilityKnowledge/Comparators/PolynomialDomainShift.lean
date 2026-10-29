module

public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShift

@[expose] public section

/-! Independent exact domain-shift target. The polynomial identity is actual
MvPolynomial substitution, and the two finite valuation maps are mutual inverses.
Arity zero and constant/zero polynomials are included, not extra hypotheses. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.PolynomialDomainShift

open PositiveExpression PolynomialCircuit
open LogicLineages.ComputabilityKnowledge.PolynomialDomainShift

def SubstitutionIdentity : Prop :=
  ∀ p : Code, interpret (shift p) =
    MvPolynomial.eval₂ MvPolynomial.C (fun i => (MvPolynomial.X i : MvPolynomial Nat Int) - 1) (interpret p)

def ArityPreserved : Prop := ∀ p : Code, (shift p).inputCount = p.inputCount

def WellFormedPreserved : Prop := ∀ p : Code, p.WellFormed → (shift p).WellFormed

def ValuationBijection : Prop :=
  ∀ (n : Nat),
    (∀ ν : Fin n → Nat, toNonnegative (toPositive ν) = ν) ∧
    (∀ ρ : Fin n → PosNat, toPositive (toNonnegative ρ) = ρ)

def ForwardEvaluation : Prop :=
  ∀ (p : Code) (ν : Fin p.inputCount → Nat),
    PolynomialComparison.evalAt (shift p) (toPositive ν) = evalNonnegative p ν

def ReverseEvaluation : Prop :=
  ∀ (p : Code) (ρ : Fin p.inputCount → PosNat),
    PolynomialComparison.evalAt (shift p) ρ = evalNonnegative p (toNonnegative ρ)

def RootEquivalence : Prop :=
  ∀ p : Code, p.WellFormed →
    (HasNonnegativeRoot p ↔ PolynomialComparison.HasPositiveRoot (shift p))

def Target : Prop := SubstitutionIdentity ∧ ArityPreserved ∧ WellFormedPreserved ∧
  ValuationBijection ∧ ForwardEvaluation ∧ ReverseEvaluation ∧ RootEquivalence

end LogicLineages.ComputabilityKnowledge.Comparators.PolynomialDomainShift
