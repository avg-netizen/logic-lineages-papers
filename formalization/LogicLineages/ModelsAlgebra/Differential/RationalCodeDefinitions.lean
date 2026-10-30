module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-! Finite rational coefficient codes for paper 15's effective conclusions.
The two natural numerators represent their difference; the stored denominator
is one less than the positive denominator. Distinct codes may denote the same
rational. All codes denote genuine rationals and all rationals are covered.
Arithmetic is explicit natural arithmetic, not an oracle on an abstract field.
-/
namespace LogicLineages.ModelsAlgebra.Differential.RationalCode

abbrev Code := (ℕ × ℕ) × ℕ

def value (c : Code) : ℚ :=
  ((c.1.1 : ℚ) - (c.1.2 : ℚ)) / ((c.2 : ℚ) + 1)

def zero : Code := ((0, 0), 0)
def one : Code := ((1, 0), 0)

def add (a b : Code) : Code :=
  ((a.1.1 * (b.2 + 1) + b.1.1 * (a.2 + 1),
    a.1.2 * (b.2 + 1) + b.1.2 * (a.2 + 1)),
    (a.2 + 1) * (b.2 + 1) - 1)

def neg (a : Code) : Code := ((a.1.2, a.1.1), a.2)

def mul (a b : Code) : Code :=
  ((a.1.1 * b.1.1 + a.1.2 * b.1.2,
    a.1.1 * b.1.2 + a.1.2 * b.1.1),
    (a.2 + 1) * (b.2 + 1) - 1)

def inverse (a : Code) : Code :=
  if a.1.1 = a.1.2 then zero
  else if a.1.2 ≤ a.1.1 then ((a.2 + 1, 0), a.1.1 - a.1.2 - 1)
  else ((0, a.2 + 1), a.1.2 - a.1.1 - 1)

def div (a b : Code) : Code := mul a (inverse b)
def isZero (a : Code) : Bool := decide (a.1.1 = a.1.2)
def equal (a b : Code) : Bool := isZero (add a (neg b))

end LogicLineages.ModelsAlgebra.Differential.RationalCode
