module

public import LogicLineages.ModelsAlgebra.Differential.LagrangeCoordinateDefinitions

@[expose] public section

/-! Literal normalized spectral coordinates and the two inverse coefficient
identities needed for the source Vandermonde change of variables. Root
injectivity is the ordinary distinct-node hypothesis, later supplied by the
original rational linear independence. No inverse matrix or jet-independence
conclusion is a premise. Full ordinary/splitting-field transport is separate.
-/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def lagrangeCoordinateNormalization : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (root : Fin n → K) (i : Fin n) (a : F),
    LagrangeCoordinate.coordinate D root i a =
      (∏ j ∈ Finset.univ.erase i, (root i - root j)⁻¹) •
        LinearOperator.coordinate D root i a

def lagrangeCoordinateEigenvalues : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (root : Fin n → K) (a : F),
    LinearOperator.applyOperator D (∏ j : Fin n, (Polynomial.X - Polynomial.C (root j))) a = 0 →
    ∀ i : Fin n, D (LagrangeCoordinate.coordinate D root i a) =
      root i • LagrangeCoordinate.coordinate D root i a

def lagrangeJetReconstruction : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (root : Fin n → K) (a : F),
    Function.Injective root → ∀ k : Fin n,
      ((D : F → F)^[k.val]) a =
        ∑ i : Fin n, root i ^ k.val • LagrangeCoordinate.coordinate D root i a

def lagrangeCoordinateFromJets : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (root : Fin n → K) (i : Fin n) (a : F),
    Function.Injective root → LagrangeCoordinate.coordinate D root i a =
      ∑ k : Fin n, (Lagrange.basis Finset.univ root i).coeff k.val •
        ((D : F → F)^[k.val]) a

def lagrangeCoefficientsLeftInverse : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K),
    Function.Injective root → ∀ i j : Fin n,
      (∑ k : Fin n, (Lagrange.basis Finset.univ root i).coeff k.val * root j ^ k.val) =
        if i = j then 1 else 0

def lagrangeCoefficientsRightInverse : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K),
    Function.Injective root → ∀ k l : Fin n,
      (∑ i : Fin n, root i ^ k.val * (Lagrange.basis Finset.univ root i).coeff l.val) =
        if k = l then 1 else 0

end LogicLineages.ModelsAlgebra.Differential.Targets
