module

public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCodeDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

open BoxPolynomialCode

def boxCodeDigitIndex : Prop := ∀ n B C k,
  digitIndex B C k n = KroneckerIndex.index C (KroneckerPolynomial.exponent B n k)

def boxCodeMonomial : Prop := ∀ a k,
  DensePolynomial.value (monomial a k) = Polynomial.C (RationalCode.value a) * Polynomial.X ^ k

def boxCodeRebase : Prop := ∀ n B C a,
  DensePolynomial.value (rebase n B C a) = KroneckerPolynomial.encode C (value n B a)

def boxCodeBound : Prop := ∀ n B, 2 ≤ B → ∀ a,
  KroneckerPolynomial.Box B (value n B a)

def boxCodeCoverage : Prop := ∀ n (p : MvPolynomial (Fin n) ℚ),
  ∃ B a, 2 ≤ B ∧ value n B a = p

def boxCodeOperationsPrimitiveRecursive : Prop :=
  Primrec (fun t : ℕ × ℕ × ℕ × ℕ => digitIndex t.1 t.2.1 t.2.2.1 t.2.2.2) ∧
  Primrec₂ monomial ∧
  Primrec (fun t : ℕ × ℕ × ℕ × Code => rebase t.1 t.2.1 t.2.2.1 t.2.2.2)

end LogicLineages.ModelsAlgebra.Differential.Targets
