module

public import LogicLineages.ModelsAlgebra.Differential.SpectralConstraintTargets
public import LogicLineages.ModelsAlgebra.Differential.GenericJets
public import LogicLineages.ModelsAlgebra.Differential.MissingSpectralModel
public import LogicLineages.ModelsAlgebra.Differential.CoefficientDescent
public import LogicLineages.ModelsAlgebra.Differential.Hyperplane
public import LogicLineages.ModelsAlgebra.Differential.IsomorphismJet
public import LogicLineages.ModelsAlgebra.Differential.OrderOne

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.SpectralConstraint

universe u

private def ordinary {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Derivation K F F) : Derivation ℤ F F where
  toLinearMap := D.toLinearMap.toAddMonoidHom.toIntLinearMap
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

private theorem jet_eq_iterate {F : Type*} [Field F] [CharZero F]
    (D : Derivation ℚ F F) (a : F) (k : ℕ) :
    jet D a k = ((D : F → F)^[k]) a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [jet, ih, Function.iterate_succ_apply']

private theorem family_restrict {K F : Type*} [Field K] [CharZero K]
    [Field F] [CharZero F] [Algebra K F] (D : Derivation K F F) (a : F) (n : ℕ) :
    FiniteJet.family (integerDerivationToRat (ordinary D)) a n =
      (fun k : Fin n => ((D : F → F)^[k.val]) a) := by
  funext k
  rw [FiniteJet.family, jet_eq_iterate]
  rfl

private theorem operator_restrict {K F : Type*} [Field K] [CharZero K]
    [Field F] [CharZero F] [Algebra K F] [IsScalarTower ℚ K F]
    (D : Derivation K F F) (f : Polynomial ℚ) (a : F) :
    LinearOperator.applyOperator (integerDerivationToRat (ordinary D)) f a =
      LinearOperator.applyOperator D (f.map (algebraMap ℚ K)) a := by
  rw [LinearOperator.literal_evaluation ℚ F, LinearOperator.literal_evaluation K F,
    Polynomial.support_map_of_injective f (algebraMap ℚ K).injective]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Polynomial.coeff_map, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  rfl

private theorem aeval_base_change {K F : Type*} [Field K] [CharZero K]
    [Field F] [CharZero F] [Algebra K F] [IsScalarTower ℚ K F]
    {ι : Type*} (x : ι → F) (q : MvPolynomial ι ℚ) :
    (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] F)
      (MvPolynomial.map (algebraMap ℚ K) q) =
      (MvPolynomial.aeval x : MvPolynomial ι ℚ →ₐ[ℚ] F) q := by
  have h : (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] F).toRingHom.comp
      (MvPolynomial.map (algebraMap ℚ K)) =
      (MvPolynomial.aeval x : MvPolynomial ι ℚ →ₐ[ℚ] F).toRingHom := by
    ext i <;> simp
  exact RingHom.congr_fun h q

private theorem source_evaluation {K F : Type*} [Field K] [CharZero K]
    [Field F] [CharZero F] [Algebra K F] [IsScalarTower ℚ K F]
    (D : Derivation K F F) (a : F) (n : ℕ) (q : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat (ordinary D)) a n) q =
      (MvPolynomial.aeval (fun k : Fin n => ((D : F → F)^[k.val]) a) :
        MvPolynomial (Fin n) K →ₐ[K] F) (MvPolynomial.map (algebraMap ℚ K) q) := by
  rw [family_restrict, aeval_base_change]

private theorem lift_aeval {F : Type} [Field F] [CharZero F] {ι : Type*}
    (x : ι → F) (q : MvPolynomial ι ℚ) :
    (MvPolynomial.aeval (fun i => (ULift.up (x i) : ULift.{u} F)) q).down =
      MvPolynomial.aeval x q := by
  exact MvPolynomial.comp_aeval_apply (fun i => (ULift.up (x i) : ULift.{u} F))
    (ULift.algEquiv (R := ℚ)).toAlgHom q

private theorem lifted_source_equation {F : Type} [Field F] [CharZero F]
    (D : Derivation ℤ F F) (a : F) (f : Polynomial ℚ)
    (ha : jetEval (integerDerivationToRat D) a (LinearOperator.linearEquation f) = 0) :
    jetEval (integerDerivationToRat (liftOrdinaryDerivation D)) (ULift.up a : ULift.{u} F)
      (LinearOperator.linearEquation f) = 0 := by
  apply ULift.ext
  have hj : jet (integerDerivationToRat (liftOrdinaryDerivation D)) (ULift.up a : ULift.{u} F) =
      fun k => (ULift.up (jet (integerDerivationToRat D) a k) : ULift.{u} F) :=
    funext (OrderOne.liftedJetEvaluation F D a)
  change (MvPolynomial.aeval
    (jet (integerDerivationToRat (liftOrdinaryDerivation D)) (ULift.up a : ULift.{u} F))
    (LinearOperator.linearEquation f) : ULift.{u} F).down = 0
  rw [hj, lift_aeval]
  exact ha

private theorem lifted_source_evaluation {F : Type} [Field F] [CharZero F]
    (D : Derivation ℤ F F) (a : F) (n : ℕ) (q : MvPolynomial (Fin n) ℚ) :
    (MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat (liftOrdinaryDerivation D))
      (ULift.up a : ULift.{u} F) n) q).down =
      MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a n) q := by
  have hj : FiniteJet.family (integerDerivationToRat (liftOrdinaryDerivation D))
      (ULift.up a : ULift.{u} F) n =
      fun k : Fin n => (ULift.up (FiniteJet.family (integerDerivationToRat D) a n k) : ULift.{u} F) :=
    funext (fun k => OrderOne.liftedJetEvaluation F D a k.val)
  rw [hj, lift_aeval]

private theorem lifted_avoidance {F : Type} [Field F] [CharZero F]
    (D : Derivation ℤ F F) (a : F) (n : ℕ) (q : MvPolynomial (Fin n) ℚ)
    (hq : MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) a n) q ≠ 0) :
    MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat (liftOrdinaryDerivation D))
      (ULift.up a : ULift.{u} F) n) q ≠ 0 := by
  intro hzero
  apply hq
  rw [← lifted_source_evaluation D a n q, hzero]
  rfl

private theorem generic_avoidance (f : Polynomial ℚ)
    (root : Fin f.natDegree → f.SplittingField) (hr : Function.Injective root)
    (q : MvPolynomial (Fin f.natDegree) ℚ) (hq : q ≠ 0) :
    MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat
      (ordinary (SpectralModel.derivation f.SplittingField f.natDegree root)))
      (SpectralModel.point f.SplittingField f.natDegree) f.natDegree) q ≠ 0 := by
  let K := f.SplittingField
  let F := SpectralModel.ModelField K f.natDegree
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  rw [family_restrict]
  have hAI := SpectralModel.generic_jets K f.natDegree root hr
  have hAIQ := AlgebraicIndependent.restrictScalars (algebraMap ℚ K).injective hAI
  have hinj : Function.Injective (MvPolynomial.aeval (fun k : Fin f.natDegree =>
      (((SpectralModel.derivation K f.natDegree root) : F → F)^[k.val]) (SpectralModel.point K f.natDegree)) :
      MvPolynomial (Fin f.natDegree) ℚ →ₐ[ℚ] F) := hAIQ
  intro hzero
  apply hq
  apply hinj
  simpa only [map_zero] using hzero

private theorem generic_equation (f : Polynomial ℚ)
    (root : Fin f.natDegree → f.SplittingField)
    (hf : f.map (algebraMap ℚ f.SplittingField) =
      ∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (root i))) :
    jetEval (integerDerivationToRat
      (ordinary (SpectralModel.derivation f.SplittingField f.natDegree root)))
      (SpectralModel.point f.SplittingField f.natDegree) (LinearOperator.linearEquation f) = 0 := by
  rw [LinearOperator.source_equation, operator_restrict, hf]
  exact SpectralModel.equation f.SplittingField f.natDegree root

private theorem missing_equation (f : Polynomial ℚ)
    (root : Fin f.natDegree → f.SplittingField)
    (hf : f.map (algebraMap ℚ f.SplittingField) =
      ∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (root i))) (skipped : Fin f.natDegree) :
    jetEval (integerDerivationToRat
      (ordinary (SpectralModel.derivation f.SplittingField f.natDegree root)))
      (SpectralModel.missingPoint f.SplittingField f.natDegree skipped) (LinearOperator.linearEquation f) = 0 := by
  rw [LinearOperator.source_equation, operator_restrict, hf]
  exact MissingSpectralModel.equation f.SplittingField f.natDegree root skipped

private theorem missing_restriction (f : Polynomial ℚ)
    (root : Fin f.natDegree → f.SplittingField) (hr : Function.Injective root)
    (R q : MvPolynomial (Fin f.natDegree) ℚ)
    (hR : MvPolynomial.map (algebraMap ℚ f.SplittingField) R = SpectralProduct.obstruction root)
    (hndiv : ¬ R ∣ q) :
    ∃ skipped : Fin f.natDegree, Hyperplane.restrictZero skipped
      (SpectralChange.toCoordinates root (MvPolynomial.map (algebraMap ℚ f.SplittingField) q)) ≠ 0 := by
  let K := f.SplittingField
  let T := SpectralChange.toCoordinates root
  have hprod : ¬ (∏ i : Fin f.natDegree, (MvPolynomial.X i : MvPolynomial (Fin f.natDegree) K)) ∣
      T (MvPolynomial.map (algebraMap ℚ K) q) := by
    intro hdvd
    have hs : (∏ i : Fin f.natDegree, SpectralProduct.scale root i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => (SpectralProduct.degree_and_scale K f.natDegree root hr i).2)
    have hu : IsUnit (MvPolynomial.C (∏ i : Fin f.natDegree, SpectralProduct.scale root i) :
        MvPolynomial (Fin f.natDegree) K) :=
      (isUnit_iff_ne_zero.mpr hs).map MvPolynomial.C
    have htrans : T (MvPolynomial.map (algebraMap ℚ K) R) ∣ T (MvPolynomial.map (algebraMap ℚ K) q) := by
      rw [hR, SpectralProduct.product_substitution K f.natDegree root hr]
      exact hu.mul_left_dvd.mpr hdvd
    obtain ⟨h, hh⟩ := htrans
    have hback : MvPolynomial.map (algebraMap ℚ K) R ∣ MvPolynomial.map (algebraMap ℚ K) q := by
      refine ⟨SpectralChange.toJets root h, ?_⟩
      have heq := congrArg (SpectralChange.toJets root) hh
      rw [map_mul] at heq
      have hleft := (SpectralChange.inverse K f.natDegree root hr).1
      simp only [T, ← AlgHom.comp_apply, hleft] at heq
      change MvPolynomial.map (algebraMap ℚ K) q =
        MvPolynomial.map (algebraMap ℚ K) R * SpectralChange.toJets root h at heq
      exact heq
    exact hndiv ((CoefficientDescent.divisibility_descent ℚ K (Fin f.natDegree) R q).mp hback)
  exact (Hyperplane.product_missing_witness K f.natDegree (T (MvPolynomial.map (algebraMap ℚ K) q))).mp hprod

theorem criterion : Targets.spectralConstraintCriterion.{u} := by
  intro f root hm hn hr hf R hR q hq
  let K := f.SplittingField
  let F := SpectralModel.ModelField K f.natDegree
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  letI : Algebra ℤ F := Ring.toIntAlgebra F
  letI : Module ℤ F := AddCommGroup.toIntModule F
  let D := ordinary (SpectralModel.derivation K f.natDegree root)
  let b := SpectralModel.point K f.natDegree
  have hb : jetEval (integerDerivationToRat D) b (LinearOperator.linearEquation f) = 0 :=
    generic_equation f root hf
  have hqb : MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) b f.natDegree) q ≠ 0 :=
    generic_avoidance f root hr.injective q hq
  constructor
  · intro hcon
    by_contra hndiv
    obtain ⟨skipped, hrestriction⟩ := missing_restriction f root hr.injective R q hR hndiv
    let c := SpectralModel.missingPoint K f.natDegree skipped
    have hc : jetEval (integerDerivationToRat D) c (LinearOperator.linearEquation f) = 0 :=
      missing_equation f root hf skipped
    have hqc : MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) c f.natDegree) q ≠ 0 := by
      rw [source_evaluation]
      exact MissingSpectralModel.avoidance K f.natDegree root hr.injective skipped _ hrestriction
    have hRc : MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat D) c f.natDegree) R = 0 := by
      rw [source_evaluation, hR]
      exact MissingSpectralModel.obstruction_zero K f.natDegree root hr.injective skipped
    have hRzero : R ≠ 0 := by
      intro hz
      have hbad : SpectralProduct.obstruction root = 0 := by rw [← hR, hz, map_zero]
      exact SpectralProduct.product_nonzero K f.natDegree root hr.injective hbad
    have hRb := generic_avoidance f root hr.injective R hRzero
    let DU : Derivation ℤ (ULift.{u} F) (ULift.{u} F) := liftOrdinaryDerivation D
    have hiso := hcon.2 (ULift.{u} F) (ULift.{u} F) DU DU (ULift.up b) (ULift.up c)
      (lifted_source_equation D b f hb) (lifted_avoidance D b f.natDegree q hqb)
      (lifted_source_equation D c f hc) (lifted_avoidance D c f.natDegree q hqc)
    have hrel := IsomorphismJet.preserves_jet_relations (ULift.{u} F) (ULift.{u} F)
      DU DU (ULift.up b) (ULift.up c) hiso f.natDegree R
    have hRcU : MvPolynomial.aeval (FiniteJet.family (integerDerivationToRat DU)
        (ULift.up c) f.natDegree) R = 0 := by
      apply ULift.ext
      exact (lifted_source_evaluation D c f.natDegree R).trans hRc
    exact lifted_avoidance D b f.natDegree R hRb (hrel.mpr hRcU)
  · intro hdvd
    refine ⟨?_, ?_⟩
    · exact ⟨ULift.{u} F, inferInstance, inferInstance, liftOrdinaryDerivation D, ULift.up b,
        lifted_source_equation D b f hb, lifted_avoidance D b f.natDegree q hqb⟩
    · intro L H _ _ _ _ E G a c ha hqa hc hqc
      have hRavoid {J : Type u} [Field J] [CharZero J] (x : Fin f.natDegree → J)
          (hx : MvPolynomial.aeval x q ≠ 0) : MvPolynomial.aeval x R ≠ 0 := by
        intro hzero
        obtain ⟨p, hp⟩ := hdvd
        apply hx
        rw [hp, map_mul, hzero, zero_mul]
      exact (GenericJets.source_generic_jets f root hm hn hr hf R hR).2
        L H E G a c ha (hRavoid _ hqa) hc (hRavoid _ hqc)

theorem complete : Targets.spectralConstraintComplete.{u} := by
  intro f root hm hn hr hf
  obtain ⟨R, hR, hRzero⟩ := SpectralDescent.rational_descent f f.natDegree root hm hr.injective hf
  have hcrit := criterion f root hm hn hr hf R hR
  exact ⟨R, hR, hRzero, (hcrit R hRzero).mpr (dvd_refl R), hcrit⟩

end LogicLineages.ModelsAlgebra.Differential.SpectralConstraint
