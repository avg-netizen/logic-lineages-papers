module

public import LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearchTargets
public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearch
public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearchEffectivity

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearch

theorem atIndex_primitive_recursive : Targets.polynomialQuotientAtIndexPrimitiveRecursive := by
  have hinput : Primrec (fun t : (Input × ℕ) × Certificate => (t.1.1, t.2)) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  have hcomposed := PolynomialCertificateSearch.verify_primitive_recursive.comp hinput
  have hverify : Primrec (fun t : (Input × ℕ) × Certificate =>
      PolynomialCertificateSearch.verify t.1.1.1 t.1.1.2 t.2) :=
    hcomposed.of_eq (fun _ => rfl)
  change Primrec (fun t : Input × ℕ => atIndex t.1 t.2)
  apply Primrec.ite
    (Primrec.eq.comp (DensePolynomial.isZero_primitive_recursive.comp
      (Primrec.fst.comp Primrec.fst)) (Primrec.const true))
    (Primrec.option_some.comp ((Primrec.const ([] : DensePolynomial.Code)).pair
      (Primrec.snd.comp Primrec.fst)))
  apply Primrec.option_bind (Primrec.decode.comp Primrec.snd)
  exact Primrec.ite
    (Primrec.eq.comp hverify (Primrec.const true))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)

theorem search_correct : Targets.polynomialQuotientSearchCorrect := by
  intro b a w hw
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hw
  by_cases hb : DensePolynomial.isZero b = true
  · have he : (([], a) : Certificate) = w := by simpa [atIndex, hb] using hn
    rw [← he]
    have hbz := (DensePolynomial.isZero_correct b).mp hb
    refine ⟨?_, fun h => False.elim (h hbz), ?_⟩
    · simp [hbz, DensePolynomial.value]
    · simpa only [hbz, zero_dvd_iff] using DensePolynomial.isZero_correct a
  · have hin : w ∈ (Encodable.decode n : Option Certificate).bind (fun v =>
        if PolynomialCertificateSearch.verify b a v then some v else none) := by
      simpa only [atIndex, if_neg hb] using hn
    obtain ⟨v, _, hv⟩ := Option.mem_bind_iff.mp hin
    by_cases hverify : PolynomialCertificateSearch.verify b a v = true
    · have he : v = w := by simpa [hverify] using hv
      rw [← he]
      have hc := (PolynomialCertificateSearch.verifier_correct b a v).mp hverify
      exact ⟨hc.1, fun _ => hc.2,
        PolynomialCertificateSearch.certificate_answer b a v hverify⟩
    · simp [hverify] at hv

theorem search_total : Targets.polynomialQuotientSearchTotal := by
  rintro ⟨b, a⟩
  apply Nat.rfindOpt_dom.mpr
  by_cases hb : DensePolynomial.isZero b = true
  · exact ⟨0, ([], a), by simp [atIndex, hb]⟩
  · have hbval : DensePolynomial.value b ≠ 0 :=
      fun h => hb ((DensePolynomial.isZero_correct b).mpr h)
    obtain ⟨w, hw⟩ := PolynomialCertificateSearch.certificate_exists b a hbval
    refine ⟨Encodable.encode w, w, ?_⟩
    simp only [atIndex, if_neg hb]
    rw [Encodable.encodek w]
    simp only [Option.bind_some, if_pos hw, Option.mem_some_iff]

theorem search_partial_recursive : Targets.polynomialQuotientSearchPartialRecursive :=
  Partrec.rfindOpt atIndex_primitive_recursive.to_comp

theorem computable_realization : Targets.polynomialQuotientComputableRealization := by
  let f : Input → Certificate := fun t => (search t).get (search_total t)
  have hf : Computable f :=
    Partrec.of_eq_tot search_partial_recursive (fun t => Part.get_mem (search_total t))
  exact ⟨f, hf, fun t => Part.get_mem (search_total t),
    fun b a => search_correct b a (f (b, a)) (Part.get_mem (search_total (b, a)))⟩

end LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearch
