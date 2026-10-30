module

public import LogicLineages.ModelsAlgebra.Differential.SpectralChangeDefinitions

@[expose] public section

/-! Direct generic-jet suppliers for paper 15. The full source lemma still
requires actual ordinary-derivation/splitting-field transport and the rational
R_f/product nonvanishing bridge. This constant-base component proves algebraic
independence, rather than taking it or an inverse substitution as a premise.
-/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u v

def spectralChangeInverse : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (root : Fin n → K), Function.Injective root →
    (SpectralChange.toJets root).comp (SpectralChange.toCoordinates root) =
      AlgHom.id K (MvPolynomial (Fin n) K) ∧
    (SpectralChange.toCoordinates root).comp (SpectralChange.toJets root) =
      AlgHom.id K (MvPolynomial (Fin n) K)

def spectralChangeCalibration : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (root : Fin n → K) (a : F),
    Function.Injective root →
    (MvPolynomial.aeval (fun i : Fin n => LagrangeCoordinate.coordinate D root i a)).comp
      (SpectralChange.toCoordinates root) =
    MvPolynomial.aeval (fun k : Fin n => ((D : F → F)^[k.val]) a)

def spectralGenericJetIndependence : Prop :=
  ∀ (K : Type u) (F : Type v) [Field K] [CharZero K] [Field F] [Algebra K F]
    (D : Derivation K F F) (n : ℕ) (root : Fin n → K) (a : F),
    LinearIndependent ℚ root →
    (∀ i : Fin n, LagrangeCoordinate.coordinate D root i a ≠ 0) →
    LinearOperator.applyOperator D (∏ i : Fin n, (Polynomial.X - Polynomial.C (root i))) a = 0 →
    AlgebraicIndependent K (fun k : Fin n => ((D : F → F)^[k.val]) a)

end LogicLineages.ModelsAlgebra.Differential.Targets
