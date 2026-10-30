module
public import LogicLineages.OrdinalComparison.BinaryMatrixDefinitions
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Literal complete source denominator over F2, retaining every factor. -/
noncomputable def actualBinarySourceDenominator (d : Nat) : Polynomial (ZMod 2) :=
  ∏ i : Fin d, (1 + Polynomial.X ^ (i.val + 1))

/-- Source coefficient-space dimension: the triangular degree of A_d. -/
def actualBinarySourceDimension (d : Nat) : Nat := d * (d + 1) / 2

end LogicLineages.OrdinalComparison
