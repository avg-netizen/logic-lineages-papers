module

public import LogicLineages.ModelsAlgebra.Differential.OrderOneAlgorithmTargets
public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch
public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearchEffectivity
public import LogicLineages.ModelsAlgebra.Differential.OrderOneDivision

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.OrderOneAlgorithm

open Polynomial
universe u

theorem input_coefficients (pc : Input) (i : ℕ) :
    (inputValue pc).coeff i = DensePolynomial.value (pc.getD i []) := by
  induction pc generalizing i with
  | nil => simp [inputValue, DensePolynomial.value]
  | cons a as ih =>
    cases i with
    | zero => simp [inputValue]
    | succ i => simpa only [inputValue, coeff_add, coeff_C_succ, coeff_X_mul,
        zero_add, List.getD_cons_succ] using ih i

private theorem input_coefficient_range (n : ℕ) (f : ℕ → DensePolynomial.Code) (i : ℕ) :
    (inputValue ((List.range n).map f)).coeff i =
      if i < n then DensePolynomial.value (f i) else 0 := by
  rw [input_coefficients]
  by_cases hi : i < n
  · rw [if_pos hi, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range]
  · rw [if_neg hi, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    rfl

theorem input_coverage : Targets.orderOneAlgorithmInputCoverage := by
  intro p q
  obtain ⟨qc, hqc⟩ := DensePolynomial.coverage q
  classical
  choose code hcode using (show ∀ r : Polynomial ℚ,
    ∃ c : DensePolynomial.Code, DensePolynomial.value c = r from DensePolynomial.coverage)
  refine ⟨(List.range (p.natDegree + 1)).map (fun i => code (p.coeff i)), qc, ?_, hqc⟩
  apply Polynomial.ext
  intro i
  rw [input_coefficient_range]
  by_cases hi : i < p.natDegree + 1
  · rw [if_pos hi, hcode]
  · rw [if_neg hi, coeff_eq_zero_of_natDegree_lt (by omega)]

theorem specialization_correct : Targets.orderOneAlgorithmSpecialization := by
  intro pc
  cases pc with
  | nil => simp [inputValue, specialization, DensePolynomial.value]
  | cons a as => simp [inputValue, specialization]

theorem search_answer_correct : Targets.orderOneAlgorithmSearchCorrect.{u} := by
  intro pc qc answer hp hdeg hq ha
  rw [OrderOneDivision.orderOneDivisionCriterion
    (inputValue pc) (DensePolynomial.value qc) hp hdeg hq, specialization_correct pc]
  by_cases hz : DensePolynomial.isZero (specialization pc) = true
  · have he : answer = false := by simpa only [search, if_pos hz, Part.mem_some_iff] using ha
    have hr := (DensePolynomial.isZero_correct _).mp hz
    simp [he, hr]
  · have hr : DensePolynomial.value (specialization pc) ≠ 0 :=
      fun h => hz ((DensePolynomial.isZero_correct _).mpr h)
    have ha' : answer ∈ PolynomialCertificateSearch.search
        (specialization pc, DensePolynomial.mul (DensePolynomial.derivative (specialization pc)) qc) := by
      simpa only [search, if_neg hz] using ha
    have h := PolynomialCertificateSearch.search_answer_correct _ _ answer ha'
    rw [and_iff_right hr]
    simpa only [DensePolynomial.value_mul, DensePolynomial.value_derivative] using h

theorem search_total : Targets.orderOneAlgorithmSearchTotal := by
  intro pc qc
  by_cases hz : DensePolynomial.isZero (specialization pc) = true
  · simp [search, hz]
  · simpa only [search, if_neg hz] using PolynomialCertificateSearch.search_total
      (specialization pc, DensePolynomial.mul (DensePolynomial.derivative (specialization pc)) qc)

private theorem specialization_primitive_recursive : Primrec specialization :=
  (Primrec.list_getD ([] : DensePolynomial.Code)).comp Primrec.id (Primrec.const 0)

theorem search_partial_recursive : Targets.orderOneAlgorithmSearchPartialRecursive := by
  have hg : Primrec (fun t : Input × DensePolynomial.Code =>
      (specialization t.1,
        DensePolynomial.mul (DensePolynomial.derivative (specialization t.1)) t.2)) :=
    (specialization_primitive_recursive.comp Primrec.fst).pair
      (DensePolynomial.mul_primitive_recursive.comp
        (DensePolynomial.derivative_primitive_recursive.comp
          (specialization_primitive_recursive.comp Primrec.fst)) Primrec.snd)
  have hs := PolynomialCertificateSearch.search_partial_recursive.comp hg.to_comp
  have hm : Primrec (fun p : (Input × DensePolynomial.Code) × Bool =>
      if DensePolynomial.isZero (specialization p.1.1) then false else p.2) :=
    Primrec.ite
      (Primrec.eq.comp (DensePolynomial.isZero_primitive_recursive.comp
        (specialization_primitive_recursive.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const true))
      (Primrec.const false) Primrec.snd
  apply (hs.map hm.to_comp.to₂).of_eq
  intro t
  by_cases hz : DensePolynomial.isZero (specialization t.1) = true
  · have hd := PolynomialCertificateSearch.search_total
      (specialization t.1,
        DensePolynomial.mul (DensePolynomial.derivative (specialization t.1)) t.2)
    simp only [search, if_pos hz]
    exact Part.eq_some_iff.mpr (Part.mem_map (fun _ => false) (Part.get_mem hd))
  · simp only [search, if_neg hz]
    exact Part.map_id' (fun _ => rfl) _

theorem computable_realization : Targets.orderOneAlgorithmComputableRealization.{u} := by
  let f : Input → DensePolynomial.Code → Bool := fun pc qc =>
    (search pc qc).get (search_total pc qc)
  have hf : Computable₂ f :=
    Partrec.of_eq_tot search_partial_recursive (fun t => Part.get_mem (search_total t.1 t.2))
  refine ⟨f, hf, ?_, ?_⟩
  · intro pc qc
    exact Part.get_mem (search_total pc qc)
  · intro pc qc hp hd hq
    exact search_answer_correct pc qc (f pc qc) hp hd hq (Part.get_mem (search_total pc qc))

end LogicLineages.ModelsAlgebra.Differential.OrderOneAlgorithm
