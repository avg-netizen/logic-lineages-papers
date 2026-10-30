module

public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivisionTargets
public import LogicLineages.ModelsAlgebra.Differential.BoxPolynomialCode
public import LogicLineages.ModelsAlgebra.Differential.PolynomialQuotientSearch

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision

private theorem box_mono {n B C : ℕ} (hBC : B ≤ C) {p : MvPolynomial (Fin n) ℚ}
    (hp : KroneckerPolynomial.Box B p) : KroneckerPolynomial.Box C p := by
  intro d hd i
  exact (hp d hd i).trans_le hBC

theorem input_coverage : Targets.boundedDivisionInputCoverage := by
  intro n p q
  obtain ⟨Bp, hBp, hp⟩ := KroneckerPolynomial.box_exists ℚ n p
  obtain ⟨Bq, hBq, hq⟩ := KroneckerPolynomial.box_exists ℚ n q
  let B := max Bp Bq
  have hB : 2 ≤ B := hBp.trans (le_max_left _ _)
  have hpB : KroneckerPolynomial.Box B p := box_mono (le_max_left _ _) hp
  have hqB : KroneckerPolynomial.Box B q := box_mono (le_max_right _ _) hq
  obtain ⟨pc, hpc⟩ := DensePolynomial.coverage (KroneckerPolynomial.encode B p)
  obtain ⟨qc, hqc⟩ := DensePolynomial.coverage (KroneckerPolynomial.encode B q)
  refine ⟨B, pc, qc, hB, ?_, ?_⟩
  · rw [BoxPolynomialCode.value, hpc]
    exact KroneckerPolynomial.decode_encode ℚ n B hB p hpB
  · rw [BoxPolynomialCode.value, hqc]
    exact KroneckerPolynomial.decode_encode ℚ n B hB q hqB

private theorem verifier_correct (n B : ℕ) (hB : 2 ≤ B)
    (pc qc : BoxPolynomialCode.Code) (w : PolynomialQuotientSearch.Certificate)
    (hw : w ∈ PolynomialQuotientSearch.search (prepare (n, B, pc, qc))) :
    verify (n, B, pc, qc) w = true ↔
      BoxPolynomialCode.value n B pc ∣ BoxPolynomialCode.value n B qc := by
  let p := BoxPolynomialCode.value n B pc
  let q := BoxPolynomialCode.value n B qc
  let h := BoxPolynomialCode.value n B w.1
  have hpB : KroneckerPolynomial.Box B p := BoxPolynomialCode.bound n B hB pc
  have hqB : KroneckerPolynomial.Box B q := BoxPolynomialCode.bound n B hB qc
  have hhB : KroneckerPolynomial.Box B h := BoxPolynomialCode.bound n B hB w.1
  have hv : verify (n, B, pc, qc) w = true ↔
      DensePolynomial.isZero w.2 = true ∧
      KroneckerPolynomial.encode (2 * B) p * KroneckerPolynomial.encode (2 * B) h =
        KroneckerPolynomial.encode (2 * B) q := by
    simp only [verify, Bool.and_eq_true, PolynomialCertificateSearch.equal_correct,
      DensePolynomial.value_mul]
    rw [BoxPolynomialCode.rebase_calibration n B (2 * B) pc,
      BoxPolynomialCode.rebase_calibration n B (2 * B) w.1,
      BoxPolynomialCode.rebase_calibration n B (2 * B) qc]
  rw [hv, KroneckerPolynomial.larger_base_verification ℚ n B hB p h q hpB hhB hqB]
  constructor
  · rintro ⟨_, heq⟩
    exact ⟨h, heq.symm⟩
  · intro hd
    change p ∣ q at hd
    change w ∈ PolynomialQuotientSearch.search
      (BoxPolynomialCode.rebase n B B pc, BoxPolynomialCode.rebase n B B qc) at hw
    have hc := PolynomialQuotientSearch.search_correct _ _ w hw
    rw [BoxPolynomialCode.rebase_calibration n B B pc,
      BoxPolynomialCode.rebase_calibration n B B qc] at hc
    have hencoded : KroneckerPolynomial.encode B p ∣ KroneckerPolynomial.encode B q := by
      obtain ⟨z, hz⟩ := hd
      refine ⟨KroneckerPolynomial.encode B z, ?_⟩
      rw [hz, map_mul]
    have hrem : DensePolynomial.isZero w.2 = true := hc.2.2.mpr hencoded
    refine ⟨hrem, ?_⟩
    by_cases hpz : p = 0
    · obtain ⟨z, hz⟩ := hd
      have hqz : q = 0 := by simpa [hpz] using hz
      simp [hpz, hqz]
    · obtain ⟨z, hz⟩ := hd
      have hzB : KroneckerPolynomial.Box B z :=
        KroneckerPolynomial.quotient_box ℚ n B hB p q z hpz hz hqB
      have hep : KroneckerPolynomial.encode B p ≠ 0 := by
        intro he
        apply hpz
        apply KroneckerPolynomial.polynomial_injective ℚ n B hB p 0 hpB
          (by intro d hd; simp at hd)
        simpa only [map_zero] using he
      have hremzero := (DensePolynomial.isZero_correct w.2).mp hrem
      have heq : KroneckerPolynomial.encode B p * DensePolynomial.value w.1 =
          KroneckerPolynomial.encode B q := by
        simpa only [hremzero, add_zero] using hc.1.symm
      have huni : DensePolynomial.value w.1 = KroneckerPolynomial.encode B z := by
        apply mul_left_cancel₀ hep
        rw [heq, hz, map_mul]
      have hh : h = z := by
        change KroneckerPolynomial.decode B n (DensePolynomial.value w.1) = z
        rw [huni]
        exact KroneckerPolynomial.decode_encode ℚ n B hB z hzB
      simpa only [hh] using hz.symm

theorem search_correct : Targets.boundedDivisionSearchCorrect := by
  intro n B hB pc qc answer ha
  obtain ⟨w, hw, heq⟩ := (Part.mem_map_iff (verify (n, B, pc, qc))).mp ha
  rw [← heq]
  exact verifier_correct n B hB pc qc w hw

theorem search_total : Targets.boundedDivisionSearchTotal := by
  intro t
  exact PolynomialQuotientSearch.search_total (prepare t)

end LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivision
