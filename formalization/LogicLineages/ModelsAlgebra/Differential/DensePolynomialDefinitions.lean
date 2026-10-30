module

public import LogicLineages.ModelsAlgebra.Differential.RationalCodeDefinitions
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section

/-! Explicit finite rational-polynomial input data for the paper 15 algorithms.
Coefficients are stored in increasing degree order; trailing zero coefficients
are permitted. The semantics is the ordinary Q-polynomial Horner expansion.
-/
namespace LogicLineages.ModelsAlgebra.Differential.DensePolynomial

abbrev Code := List RationalCode.Code

noncomputable def value : Code → Polynomial ℚ
  | [] => 0
  | a :: as => Polynomial.C (RationalCode.value a) + Polynomial.X * value as

def add (a b : Code) : Code :=
  (List.range (max a.length b.length)).map fun i =>
    RationalCode.add (a.getD i RationalCode.zero) (b.getD i RationalCode.zero)

def neg (a : Code) : Code := a.map RationalCode.neg
def scale (a : RationalCode.Code) (b : Code) : Code := b.map (RationalCode.mul a)

def mul : Code → Code → Code
  | [], _ => []
  | a :: as, b => add (scale a b) (RationalCode.zero :: mul as b)

def power (a : Code) : ℕ → Code
  | 0 => [RationalCode.one]
  | n + 1 => mul a (power a n)

def derivative (a : Code) : Code :=
  (List.range (a.length - 1)).map fun i =>
    RationalCode.mul (((i + 1, 0), 0) : RationalCode.Code)
      (a.getD (i + 1) RationalCode.zero)

def isZero (a : Code) : Bool := a.all RationalCode.isZero

end LogicLineages.ModelsAlgebra.Differential.DensePolynomial
