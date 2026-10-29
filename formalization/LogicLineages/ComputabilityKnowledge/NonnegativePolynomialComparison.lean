module

public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShift

@[expose] public section

/-! Full local nonnegative-polynomial-code construction, paper02 lines185–231.
The source polynomial is evaluated at finite natural-number inputs. Its literal
Xi−1 expansion feeds the checked positive circuit/comparison construction.
All output variables share one positive valuation; the original inputs become
ν+1 and all remaining wire/auxiliary values are existentially supplied.
This does not supply MRDP, quotient extraction, or bounded source C-vectors. -/
namespace LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparison

open PositiveExpression PolynomialCircuit PolynomialDomainShift

def circuit (p : Code) : CircuitReduction.Circuit := PolynomialComparison.circuit (shift p)
def bound (p : Code) : Nat := PolynomialComparison.bound (shift p)
def upper (p : Code) : Expr Nat := PolynomialComparison.upper (shift p)
def lower (p : Code) : Expr Nat := PolynomialComparison.lower (shift p)
def weakLower (p : Code) : Expr Nat := PolynomialComparison.weakLower (shift p)

def AgreesShiftedInputs (p : Code) (ν : Fin p.inputCount → Nat)
    (τ : Fin (bound p) → PosNat) : Prop :=
  ∀ j : Fin p.inputCount, CircuitComparison.finiteVal τ j.val = toPositive ν j

def strictOutput (p : Code) : Nat × Expr Nat × Expr Nat := (bound p,lower p,upper p)
def weakOutput (p : Code) : Nat × Expr Nat × Expr Nat := (bound p,weakLower p,upper p)

def strictCode (xs : List Nat) : Option (List Nat) :=
  (encodedShift xs).bind PolynomialComparison.strictCode

def weakCode (xs : List Nat) : Option (List Nat) :=
  (encodedShift xs).bind PolynomialComparison.weakCode

end LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparison
