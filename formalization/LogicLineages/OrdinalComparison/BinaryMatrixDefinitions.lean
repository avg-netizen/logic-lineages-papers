module
public import LogicLineages.OrdinalComparison.BinaryPolynomialWordDefinitions
public import Mathlib.Data.Matrix.Mul

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

/-- The actual first D polynomial coefficients, in their natural order. -/
def actualBinaryCoefficientVector {K : Type u} [Field K] (D : Nat)
    (U : Polynomial K) : Fin D → K := fun i => U.coeff i.val

/-- Literal matrix from paper10 lem:matrix. The guard implements the source
convention that a negative exponent has coefficient zero, rather than using
truncated natural subtraction without its necessary guard. -/
def actualBinaryTransitionMatrix {K : Type u} [Field K] (D : Nat)
    (A : Polynomial K) (b : Bool) : Matrix (Fin D) (Fin D) K :=
  fun i j => if j.val ≤ Nat.bit b i.val then A.coeff (Nat.bit b i.val - j.val) else 0

/-- Execute the actual matrix updates in least-significant-bit-first order. -/
def actualBinaryMatrixWord {K : Type u} [Field K] (D : Nat) (A : Polynomial K) :
    List Bool → (Fin D → K) → (Fin D → K)
  | [], v => v
  | b :: w, v => actualBinaryMatrixWord D A w (Matrix.mulVec (actualBinaryTransitionMatrix D A b) v)

end LogicLineages.OrdinalComparison
