module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantCodeDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Targets

def spectralOuterCodeArithmetic : Prop :=
  (∀ a b, SpectralResultantCode.outerValue (SpectralResultantCode.outerAdd a b) =
    SpectralResultantCode.outerValue a + SpectralResultantCode.outerValue b) ∧
  ∀ a k, SpectralResultantCode.outerValue (SpectralResultantCode.outerMonomial a k) =
    Polynomial.C (DensePolynomial.value a) * Polynomial.X ^ k

def spectralGeneratingCodeCorrect : Prop := ∀ n B fc,
  SpectralResultantCode.outerValue (SpectralResultantCode.generating n B fc) =
    (SpectralResultant.generating n (DensePolynomial.value fc)).map
      (KroneckerPolynomial.encode B).toRingHom

def spectralSylvesterCodeCorrect : Prop := ∀ n B fc,
  NumericDeterminant.value (n + (n - 1)) (SpectralResultantCode.matrix n B fc) =
    Polynomial.sylvester
      ((DensePolynomial.value fc).map (Polynomial.C : ℚ →+* Polynomial ℚ))
      (SpectralResultantCode.outerValue (SpectralResultantCode.generating n B fc)) n (n - 1)

def spectralObstructionCodeCorrect : Prop := ∀ n B fc,
  DensePolynomial.value (SpectralResultantCode.obstruction n B fc) =
    KroneckerPolynomial.encode B (SpectralResultant.obstruction n (DensePolynomial.value fc))

def spectralResultantCodePrimitiveRecursive : Prop :=
  Primrec₂ SpectralResultantCode.outerAdd ∧ Primrec₂ SpectralResultantCode.outerMonomial ∧
  Primrec (fun t : ℕ × ℕ × DensePolynomial.Code =>
    SpectralResultantCode.generating t.1 t.2.1 t.2.2) ∧
  Primrec (fun t : ℕ × ℕ × DensePolynomial.Code =>
    SpectralResultantCode.matrix t.1 t.2.1 t.2.2) ∧
  Primrec (fun t : ℕ × ℕ × DensePolynomial.Code =>
    SpectralResultantCode.obstruction t.1 t.2.1 t.2.2)

end LogicLineages.ModelsAlgebra.Differential.Targets
