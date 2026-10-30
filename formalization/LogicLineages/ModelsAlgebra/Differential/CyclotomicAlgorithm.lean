module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicCompleteTargets
public import LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily
public import LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithmComplete

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.CyclotomicAlgorithm

universe u

theorem coefficient_code : Targets.cyclotomicCoefficientCode := by
  intro ℓ
  apply Polynomial.ext
  intro k
  rw [DensePolynomial.coefficients (coefficients ℓ) k]
  change RationalCode.value ((List.replicate ℓ RationalCode.one).getD k RationalCode.zero) =
    (CyclotomicFamily.geometric ℚ ℓ).coeff k
  rw [CyclotomicFamily.geometric_coeff ℚ ℓ k]
  by_cases hk : k < ℓ
  · rw [if_pos hk, List.getD_eq_getElem _ _ (by simpa using hk)]
    simp only [List.getElem_replicate, RationalCode.value_one]
  · rw [if_neg hk, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hk),
      RationalCode.value_zero]

private theorem coefficients_eq_rec (ℓ : ℕ) : coefficients ℓ =
    Nat.rec (motive := fun _ => DensePolynomial.Code) [] (fun _ acc => RationalCode.one :: acc) ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    simpa only [coefficients, List.replicate_succ] using
      congrArg (fun acc : DensePolynomial.Code => RationalCode.one :: acc) ih

theorem coefficients_primitive_recursive : Primrec coefficients := by
  have hs : Primrec₂ (fun (_ : ℕ) (a : DensePolynomial.Code) => RationalCode.one :: a) :=
    Primrec.list_cons.comp (Primrec.const RationalCode.one) Primrec.snd
  have h := Primrec.nat_rec₁ ([] : DensePolynomial.Code) hs
  exact h.of_eq (fun ℓ => (coefficients_eq_rec ℓ).symm)

theorem input_primitive_recursive : Primrec input := by
  have he : Primrec (fun t : Input => t.1) := Primrec.fst
  have hb : Primrec (fun t : Input => t.2.1) := Primrec.fst.comp Primrec.snd
  have hq : Primrec (fun t : Input => t.2.2) := Primrec.snd.comp Primrec.snd
  have h := (coefficients_primitive_recursive.comp he).pair (hb.pair hq)
  exact h.of_eq (fun _ => rfl)

theorem search_total : Targets.cyclotomicAlgorithmTotal := by
  intro t
  exact SpectralAlgorithm.search_total (input t)

theorem search_partial_recursive : Targets.cyclotomicAlgorithmPartialRecursive := by
  have h := SpectralAlgorithm.search_partial_recursive.comp input_primitive_recursive.to_comp
  exact h.of_eq (fun _ => rfl)

private theorem source_correct (ℓ B : ℕ) (qc : DensePolynomial.Code) (answer : Bool)
    (hp : ℓ.Prime) (hB : 2 ≤ B)
    (hq : BoxPolynomialCode.value (CyclotomicFamily.polynomial ℓ).natDegree B qc ≠ 0)
    (ha : answer ∈ search (ℓ, B, qc)) :
    answer = true ↔ ConstrainedLinear.{u} (CyclotomicFamily.polynomial ℓ)
      (BoxPolynomialCode.value (CyclotomicFamily.polynomial ℓ).natDegree B qc) := by
  let P (f : Polynomial ℚ) : Prop :=
    2 ≤ B ∧ BoxPolynomialCode.value f.natDegree B qc ≠ 0 ∧ f.Monic ∧ 0 < f.natDegree ∧
    ∃ root : Fin f.natDegree → f.SplittingField,
      LinearIndependent ℚ root ∧ f.map (algebraMap ℚ f.SplittingField) =
        ∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (root i))
  have hP : P (CyclotomicFamily.polynomial ℓ) := by
    obtain ⟨hm, _, hn, root, hr, hf⟩ := CyclotomicFamily.prime_spectral_promise ℓ hp
    exact ⟨hB, hq, hm, hn, root, hr, hf⟩
  have he := coefficient_code ℓ
  have hpromise : SpectralAlgorithm.SourcePromise (input (ℓ, B, qc)) := by
    change P (DensePolynomial.value (coefficients ℓ))
    exact Eq.mpr (congrArg P he) hP
  have h := SpectralAlgorithm.search_correct.{u} (input (ℓ, B, qc)) answer hpromise ha
  let Q (f : Polynomial ℚ) : Prop := answer = true ↔
    ConstrainedLinear.{u} f (BoxPolynomialCode.value f.natDegree B qc)
  change Q (CyclotomicFamily.polynomial ℓ)
  exact Eq.mp (congrArg Q he) h

theorem input_coverage : Targets.cyclotomicInputCoverage := by
  intro ℓ q
  exact BoxPolynomialCode.coverage (CyclotomicFamily.polynomial ℓ).natDegree q

theorem effective_family : Targets.cyclotomicEffectiveFamily.{u} := by
  let d : Input → Bool := fun t => (search t).get (search_total t)
  have hd : Computable d :=
    Partrec.of_eq_tot search_partial_recursive (fun t => Part.get_mem (search_total t))
  exact ⟨d, hd, fun t => Part.get_mem (search_total t),
    fun ℓ hp B hB qc hq => source_correct ℓ B qc (d (ℓ, B, qc)) hp hB hq
      (Part.get_mem (search_total (ℓ, B, qc)))⟩

end LogicLineages.ModelsAlgebra.Differential.CyclotomicAlgorithm
