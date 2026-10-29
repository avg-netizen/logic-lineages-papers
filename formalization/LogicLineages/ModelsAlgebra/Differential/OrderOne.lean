module

public import LogicLineages.ModelsAlgebra.Differential.OrderOneTargets
public import LogicLineages.ModelsAlgebra.Differential.CurveIsomorphism
public import LogicLineages.ModelsAlgebra.Differential.GenericCurve
public import LogicLineages.ModelsAlgebra.Differential.Radical
public import LogicLineages.ModelsAlgebra.Differential.ZeroSpecialization

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.OrderOne

universe u v w
open Polynomial

theorem liftedOrdinaryDerivation : Targets.liftedOrdinaryDerivation.{u,v} := by
  intro F _ D x
  rfl

theorem liftedPolynomialEvaluation : Targets.liftedPolynomialEvaluation.{u,v} := by
  intro F _ _ a b p q
  constructor
  · exact CurveIsomorphism.map_pairEval (ULift.algEquiv (R := ℚ)) _ _ p
  · exact (Polynomial.aeval_algHom_apply (ULift.algEquiv (R := ℚ))
      (ULift.up a : ULift.{u} F) q).symm

theorem liftedJetEvaluation : Targets.liftedJetEvaluation.{u,v} := by
  intro F _ _ D a n
  induction n with
  | zero => rfl
  | succ n ih =>
    change liftOrdinaryDerivation D
      (jet (integerDerivationToRat (liftOrdinaryDerivation D)) (ULift.up a) n) =
      ULift.up (D (jet (integerDerivationToRat D) a n))
    rw [ih]
    rfl

variable {F : Type v} {H : Type w} [Field F] [CharZero F] [Field H] [CharZero H]

theorem lift_solution (D : Derivation ℤ F F) (a : F) (p : BivariatePolynomial)
    (h : pairEval a (D a) p = 0) :
    pairEval (ULift.up a : ULift.{u} F) (liftOrdinaryDerivation D (ULift.up a)) p = 0 := by
  apply ULift.ext
  exact ((liftedPolynomialEvaluation F a (D a) p 0).1).trans h

theorem lift_avoidance (a : F) (q : Polynomial ℚ) (h : aeval a q ≠ 0) :
    aeval (ULift.up a : ULift.{u} F) q ≠ 0 := by
  intro he
  apply h
  exact ((liftedPolynomialEvaluation F a a 0 q).2).symm.trans (congrArg ULift.down he)

theorem iso_preserves_constant (D : Derivation ℤ F F) (E : Derivation ℤ H H)
    (a : F) (b : H) (hi : HasDesignatedRootIso D E a b) (hb : E b = 0) : D a = 0 := by
  obtain ⟨e, he, hd⟩ := hi
  let x : fieldGeneratedByJets (integerDerivationToRat D) a :=
    ⟨a, IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩⟩
  have hz : generatedFieldDerivation (integerDerivationToRat E) b (e x) = 0 := by
    apply Subtype.ext
    change E (e x : H) = 0
    rw [show (e x : H) = b from he, hb]
  have hx : generatedFieldDerivation (integerDerivationToRat D) a x = 0 :=
    e.injective ((hd x).trans (hz.trans (map_zero e).symm))
  exact congrArg Subtype.val hx

theorem nonconstant_of_avoids (D : Derivation ℤ F F) (a : F)
    (p : BivariatePolynomial) (q : Polynomial ℚ) (hr : p.eval 0 ≠ 0)
    (hdiv : rationalRadical (p.eval 0) ∣ q)
    (hp : pairEval a (D a) p = 0) (hq : aeval a q ≠ 0) : D a ≠ 0 := by
  intro ha
  apply hq
  apply Radical.radicalAmbientRootVanishing F (p.eval 0) q a hr hdiv
  rw [ha] at hp
  change Polynomial.eval₂ (aeval a).toRingHom 0 p = 0 at hp
  rw [Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero] at hp
  exact hp

theorem orderOneNonzeroSpecialization : Targets.orderOneNonzeroSpecialization.{u} := by
  intro p q hp hdeg hq hr
  obtain ⟨G, fg, cg, D, a, ht, hDa, hpa, hqa⟩ := GenericCurve.genericCurveUniformWitness p hp hdeg hr
  letI : Field G := fg
  letI : CharZero G := cg
  let DG : Derivation ℤ (ULift.{u} G) (ULift.{u} G) := liftOrdinaryDerivation D
  have hpA : pairEval (ULift.up a : ULift.{u} G) (DG (ULift.up a)) p = 0 := lift_solution D a p hpa
  have hqA : aeval (ULift.up a : ULift.{u} G) q ≠ 0 := lift_avoidance a q (hqa q hq)
  constructor
  · intro hc
    by_contra hdiv
    obtain ⟨c, hpc, hqc⟩ := Radical.badConstantCurveWitness p q hr hdiv
    let E : Derivation ℤ (ULift.{u} (AlgebraicClosure ℚ)) (ULift.{u} (AlgebraicClosure ℚ)) :=
      liftOrdinaryDerivation (0 : Derivation ℤ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ))
    have hi := hc.2 (ULift.{u} G) (ULift.{u} (AlgebraicClosure ℚ)) DG E
      (ULift.up a) (ULift.up c) hpA hqA
      (lift_solution (0 : Derivation ℤ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) c p hpc)
      (lift_avoidance c q hqc)
    have hz := iso_preserves_constant DG E (ULift.up a) (ULift.up c) hi (by rfl)
    exact hDa (congrArg ULift.down hz)
  · intro hdiv
    constructor
    · exact ⟨ULift.{u} G, inferInstance, inferInstance, DG, ULift.up a, hpA, hqA⟩
    · intro F H _ _ _ _ E J b c hpb hqb hpc hqc
      exact CurveIsomorphism.curveDesignatedRootIsomorphism F H E J p b c hp hdeg
        (nonconstant_of_avoids E b p q hr hdiv hpb hqb)
        (nonconstant_of_avoids J c p q hr hdiv hpc hqc) hpb hpc

theorem orderOneZeroSpecialization : Targets.orderOneZeroSpecialization.{u} := by
  intro p q _ _ hq hr hc
  obtain ⟨a, b, hab, hpa, hpb, hqa, hqb⟩ :=
    ZeroSpecialization.zeroSpecializationTwoConstants p q hr hq
  let D : Derivation ℤ (ULift.{u} ℚ) (ULift.{u} ℚ) :=
    liftOrdinaryDerivation (0 : Derivation ℤ ℚ ℚ)
  obtain ⟨e, he, _⟩ := hc.2 (ULift.{u} ℚ) (ULift.{u} ℚ) D D
    (ULift.up a) (ULift.up b)
    (lift_solution (0 : Derivation ℤ ℚ ℚ) a p hpa) (lift_avoidance a q hqa)
    (lift_solution (0 : Derivation ℤ ℚ ℚ) b p hpb) (lift_avoidance b q hqb)
  have hroot : (algebraMap ℚ _ a) =
      (⟨ULift.up a, IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩⟩ :
        fieldGeneratedByJets (integerDerivationToRat D) (ULift.up a)) := by
    apply Subtype.ext
    apply ULift.ext
    simp
  have hv := congrArg (fun x : fieldGeneratedByJets (integerDerivationToRat D)
      (ULift.up b) => x.val.down) (e.commutes a)
  rw [hroot] at hv
  have hhe := congrArg ULift.down he
  apply hab
  simpa using hv.symm.trans hhe

theorem orderOneCriterion : Targets.orderOneCriterion.{u} := by
  intro p q hp hdeg hq
  by_cases hr : p.eval 0 = 0
  · constructor
    · intro hc
      exact (orderOneZeroSpecialization p q hp hdeg hq hr hc).elim
    · intro h
      exact (h.1 hr).elim
  · rw [orderOneNonzeroSpecialization p q hp hdeg hq hr]
    exact (and_iff_right hr).symm

end LogicLineages.ModelsAlgebra.Differential.OrderOne
