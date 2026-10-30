module

public import LogicLineages.ModelsAlgebra.Differential.SpectralProductDefinitions

@[expose] public section

/-! Exact product/nonvanishing suppliers for the original spectral theorem.
The R_f here is literally the product of the unnormalized L_i forms in the
first n jet variables. No coordinate/product evaluation or rational descent
correctness is assumed. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def spectralRawDegreeAndScale : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    ∀ i : Fin n, (SpectralProduct.rawPolynomial root i).natDegree < n ∧
      SpectralProduct.scale root i ≠ 0

def spectralLinearFormEvaluation : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (p : Polynomial K) (a : F), p.natDegree < n →
    MvPolynomial.aeval (fun k : Fin n => ((D : F → F)^[k.val]) a)
      (SpectralProduct.linearForm n p) = LinearOperator.applyOperator D p a

def spectralProductEvaluation : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (root : Fin n → K) (a : F),
    Function.Injective root →
    MvPolynomial.aeval (fun k : Fin n => ((D : F → F)^[k.val]) a)
      (SpectralProduct.obstruction root) = ∏ i : Fin n, LinearOperator.coordinate D root i a

def spectralProductNonvanishing : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (root : Fin n → K) (a : F),
    Function.Injective root →
    (MvPolynomial.aeval (fun k : Fin n => ((D : F → F)^[k.val]) a)
      (SpectralProduct.obstruction root) ≠ 0 ↔
      ∀ i : Fin n, LagrangeCoordinate.coordinate D root i a ≠ 0)

def spectralRawCoordinateSubstitution : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    ∀ i : Fin n, SpectralChange.toCoordinates root
      (SpectralProduct.linearForm n (SpectralProduct.rawPolynomial root i)) =
      MvPolynomial.C (SpectralProduct.scale root i) * MvPolynomial.X i

def spectralProductSubstitution : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    SpectralChange.toCoordinates root (SpectralProduct.obstruction root) =
      MvPolynomial.C (∏ i : Fin n, SpectralProduct.scale root i) *
        ∏ i : Fin n, MvPolynomial.X i

def spectralProductNonzero : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    SpectralProduct.obstruction root ≠ 0

end LogicLineages.ModelsAlgebra.Differential.Targets
