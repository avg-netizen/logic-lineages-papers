module

public import LogicLineages.ModelsAlgebra.Differential.SpectralModelDefinitions
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

@[expose] public section

/-! Actual generic-field suppliers for paper 15 thm:spectral existence and
lem:genericjets. The model and its derivation are literal definitions; no
nonempty model, genericity, operator equation or coordinate-calibration
correctness is assumed. Full ordinary-field/splitting transport remains. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def spectralModelVariablesIndependent : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ),
    AlgebraicIndependent K (SpectralModel.coordinateVariable K n)

def spectralModelVariableDerivative : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K) (i : Fin n),
    SpectralModel.derivation K n root (SpectralModel.coordinateVariable K n i) =
      root i • SpectralModel.coordinateVariable K n i

def spectralModelEquation : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K),
    LinearOperator.applyOperator (SpectralModel.derivation K n root)
      (∏ i : Fin n, (Polynomial.X - Polynomial.C (root i))) (SpectralModel.point K n) = 0

def spectralModelCoordinateCalibration : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    ∀ i : Fin n, LagrangeCoordinate.coordinate (SpectralModel.derivation K n root)
      root i (SpectralModel.point K n) = SpectralModel.coordinateVariable K n i

def spectralModelGenericJets : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    AlgebraicIndependent K (fun k : Fin n =>
      (((SpectralModel.derivation K n root) : SpectralModel.ModelField K n →
        SpectralModel.ModelField K n)^[k.val]) (SpectralModel.point K n))

end LogicLineages.ModelsAlgebra.Differential.Targets
