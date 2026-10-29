module

public import LogicLineages.ModelsAlgebra.Differential.CurveIsomorphismTargets
public import LogicLineages.ModelsAlgebra.Differential.CurveDifferential
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.CurveIsomorphism

open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

variable {F H : Type*} [Field F] [CharZero F] [Field H] [CharZero H]

noncomputable def pairAlgHom (a c : F) : BivariatePolynomial →ₐ[ℚ] F where
  __ := pairEval a c
  commutes' r := by simp [pairEval, Polynomial.algebraMap_apply]

theorem pairEval_mem_algebraAdjoin (a c : F) (p : BivariatePolynomial) :
    pairEval a c p ∈ Algebra.adjoin ℚ ({a, c} : Set F) := by
  let A := Algebra.adjoin ℚ ({a, c} : Set F)
  have ha : a ∈ A := Algebra.subset_adjoin (Set.mem_insert a _)
  have hc : c ∈ A := Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
  have hcoeff (q : Polynomial ℚ) : aeval a q ∈ A := by
    induction q using Polynomial.induction_on with
    | C r => simpa using A.algebraMap_mem r
    | add q r hq hr => simpa using A.add_mem hq hr
    | monomial n r hn =>
      rw [pow_succ, ← mul_assoc]
      simpa using A.mul_mem hn ha
  induction p using Polynomial.induction_on with
  | C q => simpa using hcoeff q
  | add p q hp hq => simpa using A.add_mem hp hq
  | monomial n q hn =>
    rw [pow_succ, ← mul_assoc]
    simpa using A.mul_mem hn hc

noncomputable def evalToAdjoin (a c : F) :
    BivariatePolynomial →ₐ[ℚ] Algebra.adjoin ℚ ({a, c} : Set F) :=
  (pairAlgHom a c).codRestrict _ (pairEval_mem_algebraAdjoin a c)

@[simp] theorem evalToAdjoin_coe (a c : F) (p : BivariatePolynomial) :
    (evalToAdjoin a c p : F) = pairEval a c p := rfl

theorem evalToAdjoin_surjective (a c : F) : Function.Surjective (evalToAdjoin a c) := by
  rintro ⟨x, hx⟩
  suffices ∃ p, pairEval a c p = x by
    obtain ⟨p, hp⟩ := this
    exact ⟨p, Subtype.ext hp⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with hxa | hxc
    · subst x
      exact ⟨C X, by simp⟩
    · have : x = c := Set.mem_singleton_iff.mp hxc
      subst x
      exact ⟨X, by simp⟩
  | algebraMap r => exact ⟨C (C r), by simp⟩
  | add x y hx hy hpx hpy =>
    obtain ⟨p, rfl⟩ := hpx
    obtain ⟨q, rfl⟩ := hpy
    exact ⟨p + q, map_add _ _ _⟩
  | mul x y hx hy hpx hpy =>
    obtain ⟨p, rfl⟩ := hpx
    obtain ⟨q, rfl⟩ := hpy
    exact ⟨p * q, map_mul _ _ _⟩

noncomputable def coordinateEquiv (a c : F) (b d : H)
    (hk : ∀ p, pairEval a c p = 0 ↔ pairEval b d p = 0) :
    Algebra.adjoin ℚ ({a, c} : Set F) ≃ₐ[ℚ] Algebra.adjoin ℚ ({b, d} : Set H) := by
  have hker : RingHom.ker (evalToAdjoin a c) = RingHom.ker (evalToAdjoin b d) := by
    ext p
    change evalToAdjoin a c p = 0 ↔ evalToAdjoin b d p = 0
    constructor
    · intro h
      apply Subtype.ext
      exact (hk p).mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact (hk p).mpr (congrArg Subtype.val h)
  exact (Ideal.quotientKerAlgEquivOfSurjective (evalToAdjoin_surjective a c)).symm.trans
    ((Ideal.quotientEquivAlgOfEq ℚ hker).trans
      (Ideal.quotientKerAlgEquivOfSurjective (evalToAdjoin_surjective b d)))

@[simp] theorem coordinateEquiv_eval (a c : F) (b d : H)
    (hk : ∀ p, pairEval a c p = 0 ↔ pairEval b d p = 0) (p : BivariatePolynomial) :
    coordinateEquiv a c b d hk (evalToAdjoin a c p) = evalToAdjoin b d p := by
  simp [coordinateEquiv]

noncomputable def pairFieldEquiv (a c : F) (b d : H)
    (hk : ∀ p, pairEval a c p = 0 ↔ pairEval b d p = 0) :
    IntermediateField.adjoin ℚ ({a, c} : Set F) ≃ₐ[ℚ]
      IntermediateField.adjoin ℚ ({b, d} : Set H) :=
  IsFractionRing.algEquivOfAlgEquiv (coordinateEquiv a c b d hk)

@[simp] theorem pairFieldEquiv_eval (a c : F) (b d : H)
    (hk : ∀ p, pairEval a c p = 0 ↔ pairEval b d p = 0) (p : BivariatePolynomial) :
    pairFieldEquiv a c b d hk (algebraMap _ _ (evalToAdjoin a c p)) =
      algebraMap _ _ (evalToAdjoin b d p) := by
  simp [pairFieldEquiv]

theorem map_pairEval {G : Type*} [FunLike G F H] [AlgHomClass G ℚ F H]
    (f : G) (a c : F) (p : BivariatePolynomial) :
    f (pairEval a c p) = pairEval (f a) (f c) p := by
  induction p using Polynomial.induction_on with
  | C q => simpa using (Polynomial.aeval_algHom_apply f a q).symm
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n q hn =>
    rw [pow_succ, ← mul_assoc]
    simp only [map_mul, CurveDifferential.pairEval_X] at hn ⊢
    rw [hn]

/-- Agreement on the actual adjoin generators extends to the whole field,
including inverses; no differential compatibility is assumed globally. -/
theorem compatible_on_adjoin (s : Set F)
    (dA : Derivation ℚ (IntermediateField.adjoin ℚ s) (IntermediateField.adjoin ℚ s))
    (dB : Derivation ℚ H H) (e : IntermediateField.adjoin ℚ s →ₐ[ℚ] H)
    (hgen : ∀ x (hx : x ∈ s),
      e (dA ⟨x, IntermediateField.subset_adjoin ℚ s hx⟩) =
        dB (e ⟨x, IntermediateField.subset_adjoin ℚ s hx⟩)) :
    ∀ x, e (dA x) = dB (e x) := by
  rintro ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction ℚ with
  | mem x hx => exact hgen x hx
  | algebraMap r =>
    change e (dA (algebraMap ℚ _ r)) = dB (e (algebraMap ℚ _ r))
    rw [dA.map_algebraMap, e.commutes, dB.map_algebraMap, map_zero]
  | add x y hx hy hdx hdy =>
    change e (dA (⟨x, hx⟩ + ⟨y, hy⟩)) = dB (e (⟨x, hx⟩ + ⟨y, hy⟩))
    simp only [map_add, hdx, hdy]
  | inv x hx hdx =>
    change e (dA (⟨x, hx⟩⁻¹)) = dB (e (⟨x, hx⟩⁻¹))
    simp only [Derivation.leibniz_inv, smul_eq_mul, map_mul, map_neg, map_pow,
      map_inv₀, hdx]
  | mul x y hx hy hdx hdy =>
    change e (dA (⟨x, hx⟩ * ⟨y, hy⟩)) = dB (e (⟨x, hx⟩ * ⟨y, hy⟩))
    simp only [Derivation.leibniz, smul_eq_mul, map_mul, map_add, hdx, hdy]

theorem curveDesignatedRootIsomorphism : Targets.curveDesignatedRootIsomorphism := by
  intro F H _ _ _ _ D E p a b hp hdegree hDa hEb hpa hpb
  have hka := (CurveKernel.ordinaryCurveKernelAndSeparant F D p a hp hdegree hDa hpa).1
  have hkb := (CurveKernel.ordinaryCurveKernelAndSeparant H E p b hp hdegree hEb hpb).1
  have hk : ∀ q, pairEval a (D a) q = 0 ↔ pairEval b (E b) q = 0 :=
    fun q => (hka q).trans (hkb q).symm
  obtain ⟨hclosedA, hfieldA⟩ := CurveDifferential.curveFirstJetField F D p a hp hdegree hDa hpa
  obtain ⟨hclosedB, hfieldB⟩ := CurveDifferential.curveFirstJetField H E p b hp hdegree hEb hpb
  let A := IntermediateField.adjoin ℚ ({a, D a} : Set F)
  let B := IntermediateField.adjoin ℚ ({b, E b} : Set H)
  let a₀ : A := ⟨a, IntermediateField.subset_adjoin ℚ _ (Set.mem_insert a _)⟩
  let a₁ : A := ⟨D a, IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)⟩
  let b₀ : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (Set.mem_insert b _)⟩
  let b₁ : B := ⟨E b, IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)⟩
  let dA := restrictDerivation (integerDerivationToRat D) A hclosedA
  let dB := restrictDerivation (integerDerivationToRat E) B hclosedB
  let e : A ≃ₐ[ℚ] B := pairFieldEquiv a (D a) b (E b) hk
  have he0 : e a₀ = b₀ := by
    have h0a : algebraMap (Algebra.adjoin ℚ ({a, D a} : Set F)) A
        (evalToAdjoin a (D a) (C X)) = a₀ := by
      apply Subtype.ext
      change pairEval a (D a) (C X) = a
      simp
    have h0b : algebraMap (Algebra.adjoin ℚ ({b, E b} : Set H)) B
        (evalToAdjoin b (E b) (C X)) = b₀ := by
      apply Subtype.ext
      change pairEval b (E b) (C X) = b
      simp
    have h : e (algebraMap _ A (evalToAdjoin a (D a) (C X))) =
        algebraMap _ B (evalToAdjoin b (E b) (C X)) :=
      pairFieldEquiv_eval a (D a) b (E b) hk (C X)
    rwa [h0a, h0b] at h
  have he1 : e a₁ = b₁ := by
    have h1a : algebraMap (Algebra.adjoin ℚ ({a, D a} : Set F)) A
        (evalToAdjoin a (D a) X) = a₁ := by
      apply Subtype.ext
      change pairEval a (D a) X = D a
      simp
    have h1b : algebraMap (Algebra.adjoin ℚ ({b, E b} : Set H)) B
        (evalToAdjoin b (E b) X) = b₁ := by
      apply Subtype.ext
      change pairEval b (E b) X = E b
      simp
    have h : e (algebraMap _ A (evalToAdjoin a (D a) X)) =
        algebraMap _ B (evalToAdjoin b (E b) X) :=
      pairFieldEquiv_eval a (D a) b (E b) hk X
    rwa [h1a, h1b] at h
  have hdA0 : dA a₀ = a₁ := rfl
  have hdB0 : dB b₀ = b₁ := rfl
  have hdA1 : dA a₁ = -(pairEval a₀ a₁ (partialY p) * a₁) / pairEval a₀ a₁ (separant p) := by
    apply Subtype.ext
    change D (D a) = A.val (-(pairEval a₀ a₁ (partialY p) * a₁) / pairEval a₀ a₁ (separant p))
    simp only [map_div₀, map_neg, map_mul, map_pairEval]
    exact
      CurveDifferential.curveSecondJet F D p a hp hdegree hDa hpa
  have hdB1 : dB b₁ = -(pairEval b₀ b₁ (partialY p) * b₁) / pairEval b₀ b₁ (separant p) := by
    apply Subtype.ext
    change E (E b) = B.val (-(pairEval b₀ b₁ (partialY p) * b₁) / pairEval b₀ b₁ (separant p))
    simp only [map_div₀, map_neg, map_mul, map_pairEval]
    exact
      CurveDifferential.curveSecondJet H E p b hp hdegree hEb hpb
  have hcompat : ∀ x, e (dA x) = dB (e x) := by
    apply compatible_on_adjoin ({a, D a} : Set F) dA dB e.toAlgHom
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxa | hxd
    · subst x
      change e (dA a₀) = dB (e a₀)
      rw [hdA0, he0, he1, hdB0]
    · have hxd' : x = D a := Set.mem_singleton_iff.mp hxd
      subst x
      change e (dA a₁) = dB (e a₁)
      rw [hdA1, he1, hdB1]
      simp only [map_div₀, map_neg, map_mul, map_pairEval, he0, he1]
  let u := IntermediateField.equivOfEq hfieldA.symm
  let v := IntermediateField.equivOfEq hfieldB
  let result := (u.trans e).trans v
  refine ⟨result, ?_, ?_⟩
  · change (v (e (u ⟨a, _⟩)) : H) = b
    have hu : u ⟨a, IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩⟩ = a₀ := by
      apply Subtype.ext
      rfl
    rw [hu, he0]
    rfl
  · intro x
    have hu : u (generatedFieldDerivation (integerDerivationToRat D) a x) = dA (u x) := by
      apply Subtype.ext
      rfl
    have hv (y : B) : v (dB y) = generatedFieldDerivation (integerDerivationToRat E) b (v y) := by
      apply Subtype.ext
      rfl
    change v (e (u (generatedFieldDerivation (integerDerivationToRat D) a x))) = _
    rw [hu, hcompat, hv]
    rfl

end LogicLineages.ModelsAlgebra.Differential.CurveIsomorphism
