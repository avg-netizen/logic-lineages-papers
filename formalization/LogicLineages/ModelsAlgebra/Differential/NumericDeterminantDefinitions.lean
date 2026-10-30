module

public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialDefinitions
public import LogicLineages.ModelsAlgebra.Differential.KroneckerIndexDefinitions
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Computability.Partrec

@[expose] public section

/-! An explicit finite Leibniz determinant on dense rational-polynomial entries.
Functions are enumerated by bounded base-(n+2) digits. Out-of-range functions
are rejected; repeated coordinates receive weight zero. Equality with the
actual Mathlib determinant is a separate theorem obligation. -/
namespace LogicLineages.ModelsAlgebra.Differential.NumericDeterminant

abbrev MatrixCode := List DensePolynomial.Code

def entry (n : ℕ) (m : MatrixCode) (i j : ℕ) : DensePolynomial.Code := m.getD (i * n + j) []

noncomputable def value (n : ℕ) (m : MatrixCode) :
    Matrix (Fin n) (Fin n) (Polynomial ℚ) :=
  fun i j => DensePolynomial.value (entry n m i.val j.val)

def digit (n k i : ℕ) : ℕ := (k / (n + 2) ^ i) % (n + 2)

def valid (n k : ℕ) : Bool := (List.range n).all fun i => decide (digit n k i < n)

def pairSign (a b : ℕ) : RationalCode.Code :=
  if a < b then RationalCode.one else if b < a then RationalCode.neg RationalCode.one
  else RationalCode.zero

def weight (n k : ℕ) : RationalCode.Code :=
  (List.range n).foldr (fun j acc => RationalCode.mul
    ((List.range j).foldr (fun i z =>
      RationalCode.mul (pairSign (digit n k i) (digit n k j)) z) RationalCode.one) acc)
    RationalCode.one

def product (n : ℕ) (m : MatrixCode) (k : ℕ) : DensePolynomial.Code :=
  (List.range n).foldr (fun i acc =>
    DensePolynomial.mul (entry n m (digit n k i) i) acc) [RationalCode.one]

def summand (n : ℕ) (m : MatrixCode) (k : ℕ) : DensePolynomial.Code :=
  if valid n k then DensePolynomial.scale (weight n k) (product n m k) else []

def determinant (n : ℕ) (m : MatrixCode) : DensePolynomial.Code :=
  (List.range ((n + 2) ^ n)).foldr (fun k acc =>
    DensePolynomial.add (summand n m k) acc) []

end LogicLineages.ModelsAlgebra.Differential.NumericDeterminant
