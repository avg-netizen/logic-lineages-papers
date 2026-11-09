module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Definitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Targets

/-- Literal WORD-linear QE, with every surviving word evaluated at the same
original valuation, arbitrary Boolean structure, congruences, and Nat witness. -/
def ActualWordLinearElimination : Prop := ∀ x p, linear x p = true →
  ∀ ν : Nat → Nat,
    Formula.eval ν (eliminate x p) ↔ ∃ n : Nat, Formula.eval (Function.update ν x n) p

/-- No fresh or altered named word survives. Zero coefficients remain in the
occurrence syntax, so even their explicit domains are retained. -/
def ExactOutputTokens : Prop := ∀ x p, linear x p = true → ∀ t,
  t ∈ Formula.tokens (eliminate x p) ↔ t.1 ≠ x ∧ t ∈ Formula.tokens p

def ExactOutputVariables : Prop := ∀ x p, linear x p = true → ∀ i,
  i ∈ Formula.variables (eliminate x p) ↔ i ≠ x ∧ i ∈ Formula.variables p

def ExactOriginalDomains : Prop := ∀ x p, linear x p = true → ∀ ν,
  Formula.meaningful (eliminate x p) ν ↔ Formula.meaningful p ν

def ExactDegreePreservation : Prop := ∀ D x p, linear x p = true →
  Formula.allowed D p → Formula.allowed D (eliminate x p)

/-- Domains are part of the original matrix; they are retained even beneath
negation/disjunction and cannot be replaced by a tail assumption. -/
def DomainAwareElimination : Prop := ∀ x p, linear x p = true → ∀ ν,
  (Formula.meaningful (eliminate x p) ν ∧ Formula.eval ν (eliminate x p)) ↔
    ∃ n : Nat, Formula.meaningful p (Function.update ν x n) ∧ Formula.eval (Function.update ν x n) p

def LiteralCodeCalibration : Prop := ∀ x p,
  Code.eliminate x (Formula.encode p) = Formula.encode (eliminate x p)

def ActualNumericProgram : Prop := Primrec₂ Code.eliminate

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Targets
