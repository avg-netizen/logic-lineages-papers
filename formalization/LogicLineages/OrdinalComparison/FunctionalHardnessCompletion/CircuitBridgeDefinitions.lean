module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitLinearDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.NarendranDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear
open Polynomial Narendran

/-- Standard integer-polynomial meaning of the fixed linear syntax. The
shift multiplies by fixed X, never by another unknown polynomial. -/
noncomputable def expressionPolynomial {n : Nat} (x : Fin n → ZPolynomial) :
    SignedPair.Expression n → ZPolynomial
  | .unit => 1
  | .var i => x i
  | .add a b => expressionPolynomial x a + expressionPolynomial x b
  | .neg a => -expressionPolynomial x a
  | .shift a => X * expressionPolynomial x a

noncomputable def monomialPolynomial (p : Nat → NPolynomial) (m : MonomialCode) : ZPolynomial :=
  C m.1 * X ^ m.2.1 * (match m.2.2 with | none => 1 | some i => signed (p i))
noncomputable def rowPolynomial (p : Nat → NPolynomial) (r : Row) : ZPolynomial :=
  (r.map (monomialPolynomial p)).sum

def RowsSolve (p : Nat → NPolynomial) (rs : List Row) : Prop :=
  ∀ r ∈ rs, rowPolynomial p r = 0

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear
