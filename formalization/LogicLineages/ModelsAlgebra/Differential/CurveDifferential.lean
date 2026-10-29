module

public import LogicLineages.ModelsAlgebra.Differential.CurveDifferentialTargets
public import LogicLineages.ModelsAlgebra.Differential.CurveKernel
public import LogicLineages.ModelsAlgebra.Differential.GeneratedField
public import Mathlib.Tactic.Ring

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.CurveDifferential

open Polynomial

@[simp] theorem partialY_coeff (p : BivariatePolynomial) (n : ℕ) :
    (partialY p).coeff n = (p.coeff n).derivative := rfl

@[simp] theorem partialY_C (c : Polynomial ℚ) : partialY (C c) = C c.derivative := by
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0 <;> simp [coeff_C, hn, eq_comm]

@[simp] theorem partialY_add (p q : BivariatePolynomial) :
    partialY (p + q) = partialY p + partialY q := by
  apply Polynomial.ext
  intro n
  simp

@[simp] theorem partialY_mul_X (p : BivariatePolynomial) :
    partialY (p * X) = partialY p * X := by
  apply Polynomial.ext
  intro n
  cases n with
  | zero => simp [coeff_mul_X_zero]
  | succ n => simp [coeff_mul_X]

variable {F : Type*} [Field F] [CharZero F]

@[simp] theorem pairEval_C (a b : F) (c : Polynomial ℚ) :
    pairEval a b (C c) = aeval a c := by
  simp [pairEval]

@[simp] theorem pairEval_X (a b : F) : pairEval a b X = b := by
  simp [pairEval]

theorem pairEvaluationChainRule : Targets.pairEvaluationChainRule := by
  intro F _ _ D p a b
  induction p using Polynomial.induction_on with
  | C c =>
      simp only [partialY_C, pairEval_C, separant, derivative_C, map_zero, zero_mul, add_zero]
      simpa only [integerDerivationToRat_apply, smul_eq_mul] using
        (integerDerivationToRat D).map_aeval c a
  | add p q hp hq =>
      simp only [map_add, partialY_add, separant, derivative_add] at *
      rw [hp, hq]
      ring
  | monomial n c hp =>
      rw [pow_succ, ← mul_assoc]
      simp only [map_mul, pairEval_X, D.leibniz, smul_eq_mul, partialY_mul_X,
        separant, derivative_mul, derivative_X, mul_one, map_add] at *
      rw [hp]
      ring

theorem curveSecondJet : Targets.curveSecondJet := by
  intro F _ _ D p a hp hdegree hDa hp0
  have hsep := (CurveKernel.ordinaryCurveKernelAndSeparant F D p a hp hdegree hDa hp0).2
  have hc := pairEvaluationChainRule F D p a (D a)
  rw [hp0, map_zero] at hc
  apply (eq_div_iff hsep).mpr
  have hm : pairEval a (D a) (separant p) * D (D a) =
      -(pairEval a (D a) (partialY p) * D a) :=
    eq_neg_of_add_eq_zero_right hc.symm
  simpa only [mul_comm] using hm

theorem polynomial_eval_mem (E : IntermediateField ℚ F) {a : F} (ha : a ∈ E)
    (p : Polynomial ℚ) : aeval a p ∈ E := by
  induction p using Polynomial.induction_on with
  | C c => simpa using E.algebraMap_mem c
  | add p q hp hq => simpa only [map_add] using E.add_mem hp hq
  | monomial n c hp =>
      rw [pow_succ, ← mul_assoc]
      simpa using E.mul_mem hp ha

theorem pairEval_mem (E : IntermediateField ℚ F) {a b : F} (ha : a ∈ E) (hb : b ∈ E)
    (p : BivariatePolynomial) : pairEval a b p ∈ E := by
  induction p using Polynomial.induction_on with
  | C c => simpa using polynomial_eval_mem E ha c
  | add p q hp hq => simpa only [map_add] using E.add_mem hp hq
  | monomial n c hp =>
      rw [pow_succ, ← mul_assoc]
      simpa only [map_mul, pairEval_X] using E.mul_mem hp hb

theorem curveFirstJetField : Targets.curveFirstJetField := by
  intro F _ _ D p a hp hdegree hDa hp0
  let E := firstJetField D a
  have ha : a ∈ E := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert a _)
  have hDaE : D a ∈ E := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)
  have hDDa : D (D a) ∈ E := by
    rw [curveSecondJet F D p a hp hdegree hDa hp0]
    exact E.div_mem (E.neg_mem (E.mul_mem (pairEval_mem E ha hDaE (partialY p)) hDaE))
      (pairEval_mem E ha hDaE (separant p))
  have hclosed : IsDerivationClosed (integerDerivationToRat D) E := by
    apply adjoin_isDerivationClosed
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxa | hx
    · subst x
      exact hDaE
    · have hx' : x = D a := Set.mem_singleton_iff.mp hx
      subst x
      exact hDDa
  refine ⟨hclosed, le_antisymm ?_ ?_⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxa | hx
    · subst x
      exact self_mem_fieldGeneratedByJets (integerDerivationToRat D) a
    · have hx' : x = D a := Set.mem_singleton_iff.mp hx
      subst x
      exact IntermediateField.subset_adjoin ℚ _ ⟨1, rfl⟩
  · exact fieldGeneratedByJets_le (integerDerivationToRat D) a E ha hclosed

end LogicLineages.ModelsAlgebra.Differential.CurveDifferential
