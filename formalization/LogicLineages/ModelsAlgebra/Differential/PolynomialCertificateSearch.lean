module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearchTargets
public import LogicLineages.ModelsAlgebra.Differential.DensePolynomial

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch

open Polynomial

theorem degree_correct : Targets.polynomialCodeDegreeCorrect := by
  intro a
  by_cases ha : DensePolynomial.value a = 0
  · rw [ha, natDegree_zero]
    unfold degree
    apply Nat.findGreatest_eq_zero_iff.mpr
    intro i _ _ hi
    have hv : RationalCode.value (a.getD i RationalCode.zero) = 0 := by
      rw [← DensePolynomial.coefficients, ha]
      simp
    have ht := (RationalCode.isZero_correct _).mpr hv
    cases ht.symm.trans hi
  · have hlen : (DensePolynomial.value a).natDegree < a.length := by
      by_contra h
      have hz := DensePolynomial.coefficient_outside a
        (DensePolynomial.value a).natDegree (Nat.le_of_not_gt h)
      exact (leadingCoeff_ne_zero.mpr ha) (by simpa only [coeff_natDegree] using hz)
    let P : ℕ → Prop := fun i => RationalCode.isZero (a.getD i RationalCode.zero) = false
    have hP : P (DensePolynomial.value a).natDegree := by
      apply Bool.eq_false_iff.mpr
      intro h
      have hz := (RationalCode.isZero_correct _).mp h
      have hz' : (DensePolynomial.value a).coeff (DensePolynomial.value a).natDegree = 0 := by
        rw [DensePolynomial.coefficients]
        exact hz
      exact (leadingCoeff_ne_zero.mpr ha) (by simpa only [coeff_natDegree] using hz')
    have hlo : (DensePolynomial.value a).natDegree ≤ degree a :=
      Nat.le_findGreatest (P := P) (by omega) hP
    have htop : P (degree a) := Nat.findGreatest_spec (P := P) (by omega) hP
    have hcoef : (DensePolynomial.value a).coeff (degree a) ≠ 0 := by
      rw [DensePolynomial.coefficients]
      intro hz
      have ht := (RationalCode.isZero_correct _).mpr hz
      cases ht.symm.trans htop
    exact le_antisymm (le_natDegree_of_ne_zero hcoef) hlo

theorem equal_correct (a b : DensePolynomial.Code) :
    equal a b = true ↔ DensePolynomial.value a = DensePolynomial.value b := by
  rw [equal, DensePolynomial.isZero_correct, DensePolynomial.value_add,
    DensePolynomial.value_neg, ← sub_eq_add_neg, sub_eq_zero]

theorem verifier_correct : Targets.polynomialCertificateVerifierCorrect := by
  intro b a w
  simp only [verify, Bool.and_eq_true, equal_correct, DensePolynomial.value_add,
    DensePolynomial.value_mul, Bool.or_eq_true, DensePolynomial.isZero_correct,
    decide_eq_true_eq, degree_correct w.2, degree_correct b]

theorem certificate_exists : Targets.polynomialCertificateExists := by
  intro b a hb
  obtain ⟨q, hq⟩ := DensePolynomial.coverage (DensePolynomial.value a / DensePolynomial.value b)
  obtain ⟨r, hr⟩ := DensePolynomial.coverage (DensePolynomial.value a % DensePolynomial.value b)
  refine ⟨(q, r), (verifier_correct b a (q, r)).mpr ?_⟩
  change DensePolynomial.value a =
    DensePolynomial.value b * DensePolynomial.value q + DensePolynomial.value r ∧ _
  rw [hq, hr]
  refine ⟨(EuclideanDomain.div_add_mod _ _).symm, ?_⟩
  by_cases hz : DensePolynomial.value a % DensePolynomial.value b = 0
  · exact Or.inl hz
  · exact Or.inr ((natDegree_lt_natDegree_iff hz).mpr (Polynomial.degree_mod_lt _ hb))

theorem certificate_answer (b a : DensePolynomial.Code) (w : Certificate)
    (hw : verify b a w = true) :
    DensePolynomial.isZero w.2 = true ↔ DensePolynomial.value b ∣ DensePolynomial.value a := by
  obtain ⟨heq, hdeg⟩ := (verifier_correct b a w).mp hw
  rw [DensePolynomial.isZero_correct]
  constructor
  · intro hr
    rw [heq, hr, add_zero]
    exact dvd_mul_right _ _
  · intro hd
    have hrdiv : DensePolynomial.value b ∣ DensePolynomial.value w.2 := by
      have hh := dvd_sub hd (dvd_mul_right (DensePolynomial.value b) (DensePolynomial.value w.1))
      have hs : DensePolynomial.value a -
          DensePolynomial.value b * DensePolynomial.value w.1 = DensePolynomial.value w.2 := by
        rw [heq]
        ring
      rwa [hs] at hh
    rcases hdeg with hz | hlt
    · exact hz
    · by_contra hz
      exact (not_le_of_gt hlt) (natDegree_le_of_dvd hrdiv hz)

theorem search_answer_correct : Targets.polynomialSearchAnswerCorrect := by
  intro b a answer ha
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec ha
  by_cases hb : DensePolynomial.isZero b = true
  · have he : DensePolynomial.isZero a = answer := by simpa [atIndex, hb] using hn
    rw [← he, DensePolynomial.isZero_correct]
    rw [(DensePolynomial.isZero_correct b).mp hb, zero_dvd_iff]
  · have hin : answer ∈ (Encodable.decode n : Option Certificate).bind (fun w =>
        if verify b a w then some (DensePolynomial.isZero w.2) else none) := by
      simpa only [atIndex, if_neg hb] using hn
    obtain ⟨w, _, hw⟩ := Option.mem_bind_iff.mp hin
    by_cases hv : verify b a w = true
    · have he : DensePolynomial.isZero w.2 = answer := by simpa [hv] using hw
      rw [← he]
      exact certificate_answer b a w hv
    · simp [hv] at hw

theorem search_total : Targets.polynomialSearchTotal := by
  rintro ⟨b, a⟩
  apply Nat.rfindOpt_dom.mpr
  by_cases hb : DensePolynomial.isZero b = true
  · exact ⟨0, DensePolynomial.isZero a, by simp [atIndex, hb]⟩
  · have hbval : DensePolynomial.value b ≠ 0 :=
      fun h => hb ((DensePolynomial.isZero_correct b).mpr h)
    obtain ⟨w, hw⟩ := certificate_exists b a hbval
    refine ⟨Encodable.encode w, DensePolynomial.isZero w.2, ?_⟩
    simp only [atIndex, if_neg hb]
    rw [Encodable.encodek w]
    simp only [Option.bind_some, if_pos hw, Option.mem_some_iff]

end LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch
