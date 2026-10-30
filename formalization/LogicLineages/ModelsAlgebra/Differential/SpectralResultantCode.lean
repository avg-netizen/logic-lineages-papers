module

public import LogicLineages.ModelsAlgebra.Differential.SpectralGeneratingCode
public import LogicLineages.ModelsAlgebra.Differential.SpectralSylvesterCode
public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminant

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode

open Polynomial

theorem obstruction_correct : Targets.spectralObstructionCodeCorrect := by
  intro n B fc
  rw [obstruction,
    NumericDeterminant.determinant_correct (n + (n - 1)) (matrix n B fc),
    sylvester_correct n B fc, generating_correct n B fc]
  change ((DensePolynomial.value fc).map (Polynomial.C : ℚ →+* Polynomial ℚ)).resultant
    ((SpectralResultant.generating n (DensePolynomial.value fc)).map
      (KroneckerPolynomial.encode B).toRingHom) n (n - 1) = _
  have hf : (DensePolynomial.value fc).map (Polynomial.C : ℚ →+* Polynomial ℚ) =
      ((DensePolynomial.value fc).map
        (MvPolynomial.C : ℚ →+* MvPolynomial (Fin n) ℚ)).map
          (KroneckerPolynomial.encode B).toRingHom := by
    rw [Polynomial.map_map]
    apply congrArg (fun ψ : ℚ →+* Polynomial ℚ => (DensePolynomial.value fc).map ψ)
    apply RingHom.ext
    intro q
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      KroneckerPolynomial.encode, MvPolynomial.aeval_C, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self_apply]
  rw [hf, resultant_map_map]
  rfl

end LogicLineages.ModelsAlgebra.Differential.SpectralResultantCode
