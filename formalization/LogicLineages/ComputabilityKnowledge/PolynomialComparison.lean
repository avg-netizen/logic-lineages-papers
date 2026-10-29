module

public import LogicLineages.ComputabilityKnowledge.PolynomialCircuit
public import LogicLineages.ComputabilityKnowledge.CircuitComparison

@[expose] public section

/-! Full local positive-polynomial-code reduction, paper02 lines191–231.
Input semantics use the actual Mathlib integer polynomial. A single finite
positive valuation interprets both output terms. Arity zero and the zero
polynomial are retained. This does not assert MRDP, variable-domain conversion,
Pi01-completeness or admissible source-vector correspondence. -/
namespace LogicLineages.ComputabilityKnowledge.PolynomialComparison

open PositiveExpression PolynomialCircuit

def circuit (p : Code) : CircuitReduction.Circuit := PolynomialCircuit.compile p

def bound (p : Code) : Nat := CircuitReduction.variableBound (circuit p)
def upper (p : Code) : Expr Nat := CircuitComparison.upper (circuit p)
def lower (p : Code) : Expr Nat := CircuitComparison.lower (circuit p)
def weakLower (p : Code) : Expr Nat := CircuitComparison.weakLower (circuit p)

noncomputable def evalAt (p : Code) (ρ : Fin p.inputCount → PosNat) : Int :=
  MvPolynomial.eval (fun i => ((CircuitComparison.finiteVal ρ i).val : Int)) (interpret p)

def HasPositiveRoot (p : Code) : Prop := ∃ ρ : Fin p.inputCount → PosNat, evalAt p ρ = 0

def AgreesInputs (p : Code) (ρ : Fin p.inputCount → PosNat)
    (τ : Fin (bound p) → PosNat) : Prop :=
  ∀ j : Fin p.inputCount, CircuitComparison.finiteVal τ j.val = ρ j

def strictOutput (p : Code) : Nat × Expr Nat × Expr Nat := (bound p,lower p,upper p)
def weakOutput (p : Code) : Nat × Expr Nat × Expr Nat := (bound p,weakLower p,upper p)

/-- Literal compositions of the two concrete code transformers. -/
def strictCode (xs : List Nat) : Option (List Nat) :=
  (PolynomialCircuit.compileCode xs).bind CircuitComparison.strictCode

def weakCode (xs : List Nat) : Option (List Nat) :=
  (PolynomialCircuit.compileCode xs).bind CircuitComparison.weakCode

end LogicLineages.ComputabilityKnowledge.PolynomialComparison
