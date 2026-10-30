module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomialDefinitions
public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Finite rational multivariate data, with an explicit finite coordinate box.
The code is a dense rational polynomial whose low base-B digits specify the
exponent vector. Rebasing computes a literal univariate substitution; it does
not assume global injectivity of the Kronecker map. -/
namespace LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode

abbrev Code := DensePolynomial.Code

noncomputable def value (n B : ℕ) (a : Code) : MvPolynomial (Fin n) ℚ :=
  KroneckerPolynomial.decode B n (DensePolynomial.value a)

def digitIndex (B C k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => digitIndex B C k n + ((k / B ^ n) % B) * C ^ n

def monomial (a : RationalCode.Code) (k : ℕ) : Code :=
  DensePolynomial.scale a (DensePolynomial.power [RationalCode.zero, RationalCode.one] k)

def rebaseAux (n B C : ℕ) (a : Code) : ℕ → Code
  | 0 => []
  | k + 1 => DensePolynomial.add (rebaseAux n B C a k)
      (monomial (a.getD k RationalCode.zero) (digitIndex B C k n))

def rebase (n B C : ℕ) (a : Code) : Code := rebaseAux n B C a (B ^ n)

end LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode
