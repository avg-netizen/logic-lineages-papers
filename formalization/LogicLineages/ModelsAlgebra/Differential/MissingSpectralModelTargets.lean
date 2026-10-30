module

public import LogicLineages.ModelsAlgebra.Differential.MissingSpectralModelDefinitions
public import LogicLineages.ModelsAlgebra.Differential.SpectralProductDefinitions

@[expose] public section

/-! Actual missing-coordinate solution suppliers in the negative branch of
paper 15 thm:spectral. The source equation, coordinate calibration, zero R_f
and avoidance are all conclusions, with no witness or relation oracle. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def missingSpectralModelEquation : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K) (skipped : Fin n),
    LinearOperator.applyOperator (SpectralModel.derivation K n root)
      (∏ i : Fin n, (Polynomial.X - Polynomial.C (root i)))
      (SpectralModel.missingPoint K n skipped) = 0

def missingSpectralModelCoordinates : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    ∀ (skipped i : Fin n), LagrangeCoordinate.coordinate (SpectralModel.derivation K n root)
      root i (SpectralModel.missingPoint K n skipped) =
      if i = skipped then 0 else SpectralModel.coordinateVariable K n i

def missingSpectralModelCalibration : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    ∀ (skipped : Fin n) (q : MvPolynomial (Fin n) K),
      MvPolynomial.aeval (fun k : Fin n =>
        (((SpectralModel.derivation K n root) : SpectralModel.ModelField K n →
          SpectralModel.ModelField K n)^[k.val]) (SpectralModel.missingPoint K n skipped)) q =
      MvPolynomial.aeval (SpectralModel.coordinateVariable K n)
        (Hyperplane.restrictZero skipped (SpectralChange.toCoordinates root q))

def missingSpectralModelObstructionZero : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    ∀ skipped : Fin n, MvPolynomial.aeval (fun k : Fin n =>
      (((SpectralModel.derivation K n root) : SpectralModel.ModelField K n →
        SpectralModel.ModelField K n)^[k.val]) (SpectralModel.missingPoint K n skipped))
      (SpectralProduct.obstruction root) = 0

def missingSpectralModelAvoidance : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    ∀ (skipped : Fin n) (q : MvPolynomial (Fin n) K),
      Hyperplane.restrictZero skipped (SpectralChange.toCoordinates root q) ≠ 0 →
      MvPolynomial.aeval (fun k : Fin n =>
        (((SpectralModel.derivation K n root) : SpectralModel.ModelField K n →
          SpectralModel.ModelField K n)^[k.val]) (SpectralModel.missingPoint K n skipped)) q ≠ 0

end LogicLineages.ModelsAlgebra.Differential.Targets
