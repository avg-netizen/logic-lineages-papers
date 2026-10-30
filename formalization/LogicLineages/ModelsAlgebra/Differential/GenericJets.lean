module

public import LogicLineages.ModelsAlgebra.Differential.GenericJetsTargets
public import LogicLineages.ModelsAlgebra.Differential.SpectralDescent
public import LogicLineages.ModelsAlgebra.Differential.AlgebraicExtension
public import LogicLineages.ModelsAlgebra.Differential.AlgebraicBase
public import LogicLineages.ModelsAlgebra.Differential.MonicRecurrence

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.GenericJets

private theorem jet_eq_iterate {F : Type*} [Field F] [CharZero F]
    (D : Derivation ℚ F F) (a : F) (k : ℕ) :
    jet D a k = ((D : F → F)^[k]) a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [jet, ih, Function.iterate_succ_apply']

private theorem jet_map {F L : Type*} [Field F] [CharZero F] [Field L] [CharZero L]
    [Algebra F L] (D : Derivation ℤ F F) (E : Derivation ℤ L L)
    (hE : ∀ x, E (algebraMap F L x) = algebraMap F L (D x)) (a : F) (k : ℕ) :
    jet (integerDerivationToRat E) (algebraMap F L a) k =
      algebraMap F L (jet (integerDerivationToRat D) a k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change E (jet (integerDerivationToRat E) (algebraMap F L a) k) = _
    rw [ih, hE]
    rfl

private theorem operator_base_change {K L : Type*} [Field K] [CharZero K]
    [Field L] [CharZero L] [Algebra K L] [IsScalarTower ℚ K L]
    [Algebra.IsAlgebraic ℚ K] (E : Derivation ℤ L L) (f : Polynomial ℚ) (a : L) :
    LinearOperator.applyOperator (AlgebraicBase.toAlgebraicBase (K := K) E)
      (f.map (algebraMap ℚ K)) a =
      LinearOperator.applyOperator (integerDerivationToRat E) f a := by
  rw [LinearOperator.literal_evaluation K L, LinearOperator.literal_evaluation ℚ L,
    Polynomial.support_map_of_injective f (algebraMap ℚ K).injective]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Polynomial.coeff_map, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  rfl

private theorem aeval_base_change {K L : Type*} [Field K] [CharZero K]
    [Field L] [CharZero L] [Algebra K L] [IsScalarTower ℚ K L]
    {ι : Type*} (y : ι → L) (R : MvPolynomial ι ℚ) :
    (MvPolynomial.aeval y : MvPolynomial ι K →ₐ[K] L)
      (MvPolynomial.map (algebraMap ℚ K) R) =
      (MvPolynomial.aeval y : MvPolynomial ι ℚ →ₐ[ℚ] L) R := by
  have h : (MvPolynomial.aeval y : MvPolynomial ι K →ₐ[K] L).toRingHom.comp
      (MvPolynomial.map (algebraMap ℚ K)) =
      (MvPolynomial.aeval y : MvPolynomial ι ℚ →ₐ[ℚ] L).toRingHom := by
    ext i <;> simp [← IsScalarTower.algebraMap_apply]
  exact RingHom.congr_fun h R

theorem independent (f : Polynomial ℚ) (root : Fin f.natDegree → f.SplittingField)
    (hr : LinearIndependent ℚ root)
    (hf : f.map (algebraMap ℚ f.SplittingField) =
      ∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (root i)))
    (R : MvPolynomial (Fin f.natDegree) ℚ)
    (hR : MvPolynomial.map (algebraMap ℚ f.SplittingField) R = SpectralProduct.obstruction root)
    {F : Type*} [Field F] [CharZero F] (D : Derivation ℤ F F) (a : F)
    (ha : jetEval (integerDerivationToRat D) a (LinearOperator.linearEquation f) = 0)
    (hRa : MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a f.natDegree) R ≠ 0) :
    AlgebraicIndependent ℚ (FiniteJet.family (integerDerivationToRat D) a f.natDegree) := by
  let K := f.SplittingField
  let L := AlgebraicClosure F
  letI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  let κ : K →ₐ[ℚ] L := IsAlgClosed.lift
  letI : Algebra K L := κ.toRingHom.toAlgebra
  letI : IsScalarTower ℚ K L := IsScalarTower.of_algHom κ
  obtain ⟨E, hE, _⟩ := AlgebraicExtension.algebraicClosureDerivationExtension F D
  let dK := AlgebraicBase.toAlgebraicBase (K := K) E
  let aL := algebraMap F L a
  let j : F →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ F L
  have hj (k : ℕ) : jet (integerDerivationToRat E) aL k = j (jet (integerDerivationToRat D) a k) :=
    jet_map D E hE a k
  have hjetHom : jetEval (integerDerivationToRat E) aL = j.comp (jetEval (integerDerivationToRat D) a) := by
    apply MvPolynomial.algHom_ext
    intro k
    simpa only [jetEval, MvPolynomial.aeval_X, AlgHom.comp_apply] using hj k
  have hsol : LinearOperator.applyOperator dK
      (∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (root i))) aL = 0 := by
    rw [← hf, operator_base_change]
    rw [← LinearOperator.source_equation, hjetHom]
    simp only [AlgHom.comp_apply, ha, map_zero]
  have hy (k : Fin f.natDegree) : ((dK : L → L)^[k.val]) aL =
      j (FiniteJet.family (integerDerivationToRat D) a f.natDegree k) := by
    change (((integerDerivationToRat E) : L → L)^[k.val]) aL = _
    rw [← jet_eq_iterate]
    exact hj k.val
  have hRclosed : (MvPolynomial.aeval (fun k : Fin f.natDegree => ((dK : L → L)^[k.val]) aL))
      (SpectralProduct.obstruction root) ≠ 0 := by
    rw [← hR, aeval_base_change]
    have heval : (MvPolynomial.aeval (fun k : Fin f.natDegree => ((dK : L → L)^[k.val]) aL) :
        MvPolynomial (Fin f.natDegree) ℚ →ₐ[ℚ] L) =
        j.comp (MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a f.natDegree)) := by
      apply MvPolynomial.algHom_ext
      intro k
      simpa only [MvPolynomial.aeval_X, AlgHom.comp_apply] using hy k
    rw [heval]
    simpa only [AlgHom.comp_apply, map_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using j.injective.ne hRa
  have hx := (SpectralProduct.product_nonvanishing K L dK f.natDegree root aL hr.injective).mp hRclosed
  have hAI := SpectralChange.generic_jet_independence K L dK f.natDegree root aL hr hx hsol
  have hAIQ : AlgebraicIndependent ℚ (fun k : Fin f.natDegree => ((dK : L → L)^[k.val]) aL) :=
    AlgebraicIndependent.restrictScalars (algebraMap ℚ K).injective hAI
  have hfamily : (fun k : Fin f.natDegree => ((dK : L → L)^[k.val]) aL) =
      j ∘ FiniteJet.family (integerDerivationToRat D) a f.natDegree := funext hy
  rw [hfamily] at hAIQ
  exact AlgebraicIndependent.of_comp j hAIQ

theorem source_generic_jets : Targets.spectralGenericJets := by
  intro f root hm hn hr hf R hR
  constructor
  · intro F _ _ D a ha hRa
    exact independent f root hr hf R hR D a ha hRa
  · intro F H _ _ _ _ D E a b ha hRa hb hRb
    exact MonicRecurrence.independent_solution_isomorphism F H D E f a b hm hn ha hb
      (independent f root hr hf R hR D a ha hRa)
      (independent f root hr hf R hR E b hb hRb)

end LogicLineages.ModelsAlgebra.Differential.GenericJets
