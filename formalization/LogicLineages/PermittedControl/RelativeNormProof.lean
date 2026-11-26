module
public import LogicLineages.PermittedControl.RelativeNormTargets
public import LogicLineages.OrdinalComparison.CompatiblePrefixNormProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem filtered_fold_le (l : List (Ordinal.{0} × Ordinal.{0})) (e : Ordinal.{0}) :
    ((l.filter (fun p => e ≤ p.1)).foldr
      (fun p r => Ordinal.omega0 ^ p.1 * p.2 + r) 0) ≤
    l.foldr (fun p r => Ordinal.omega0 ^ p.1 * p.2 + r) 0 := by
  induction l with
  | nil => exact le_rfl
  | cons p l ih =>
    by_cases h : e ≤ p.1
    · simpa [List.filter_cons, h] using ih
    · simpa [List.filter_cons, h] using ih.trans (le_add_self :
        l.foldr (fun p r => Ordinal.omega0 ^ p.1 * p.2 + r) 0 ≤
        Ordinal.omega0 ^ p.1 * p.2 + l.foldr (fun p r => Ordinal.omega0 ^ p.1 * p.2 + r) 0)

 theorem relativePrefix_le (mu e : Ordinal.{0}) : relativePrefix mu e ≤ mu := by
  simpa [relativePrefix, Ordinal.CNF.foldr] using filtered_fold_le (Ordinal.CNF Ordinal.omega0 mu) e

private theorem raw_prefix_cnf (a : ONote) (ha : ONote.NF a) (e : Ordinal.{0}) :
    Ordinal.CNF Ordinal.omega0 (relativePrefix a.repr e) =
      (Ordinal.CNF Ordinal.omega0 a.repr).filter (fun p => e ≤ p.1) := by
  induction a with
  | zero => simp [relativePrefix, ONote.repr]
  | oadd f c t ihf iht =>
    have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
    have hcnf : Ordinal.CNF Ordinal.omega0 (ONote.oadd f c t).repr =
        (f.repr, ((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr :=
      Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc
        (Ordinal.natCast_lt_omega0 _) ha.snd'.repr_lt
    have htail : relativePrefix t.repr e < Ordinal.omega0 ^ f.repr :=
      (relativePrefix_le _ _).trans_lt ha.snd'.repr_lt
    by_cases he : e ≤ f.repr
    · have hp : relativePrefix (ONote.oadd f c t).repr e =
          Ordinal.omega0 ^ f.repr * (c : Nat) + relativePrefix t.repr e := by
        simp only [relativePrefix, hcnf]
        simp [he]
      rw [hp, Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc
        (Ordinal.natCast_lt_omega0 _) htail, iht ha.snd]
      rw [hcnf]
      simp [he]
    · have hp : relativePrefix (ONote.oadd f c t).repr e = relativePrefix t.repr e := by
        simp only [relativePrefix, hcnf]
        simp [he]
      rw [hp, iht ha.snd]
      rw [hcnf]
      simp [he]

 theorem relativePrefix_cnf (mu e : Ordinal.{0}) (hmu : mu < epsilonZero) :
    Ordinal.CNF Ordinal.omega0 (relativePrefix mu e) =
      (Ordinal.CNF Ordinal.omega0 mu).filter (fun p => e ≤ p.1) := by
  obtain ⟨a, rfl⟩ := normalRepresentationComplete mu hmu
  exact raw_prefix_cnf a.1 a.2 e

private theorem filtered_weight_le (l : List (Ordinal.{0} × Ordinal.{0})) (e : Ordinal.{0}) :
    ((l.filter (fun p => e ≤ p.1)).map
      (fun p => p.2.card.toNat * (1 + actualOrdinalNorm p.1))).sum ≤
    (l.map (fun p => p.2.card.toNat * (1 + actualOrdinalNorm p.1))).sum := by
  induction l with
  | nil => exact le_rfl
  | cons p l ih =>
    by_cases h : e ≤ p.1
    · simpa [h] using Nat.add_le_add_left ih (p.2.card.toNat * (1 + actualOrdinalNorm p.1))
    · simpa [h] using ih.trans (Nat.le_add_left _ _)

 theorem relativePrefixNorm : Targets.RelativePrefixNorm := by
  intro mu e hmu
  have hp := (relativePrefix_le mu e).trans_lt hmu
  have heq : relativeProfile mu e =
      (((Ordinal.CNF Ordinal.omega0 mu).filter (fun p => e ≤ p.1)).map
      (fun p => p.2.card.toNat * (1 + actualOrdinalNorm p.1))).sum := by
    rw [relativeProfile, actualOrdinalNorm_cnfEquation _ hp, relativePrefix_cnf mu e hmu]
  refine ⟨hp, heq, ?_⟩
  rw [heq, actualOrdinalNorm_cnfEquation mu hmu]
  exact filtered_weight_le _ _

private theorem prefix_zero_of_small (mu e : Ordinal.{0}) (h : mu < Ordinal.omega0 ^ e) :
    relativePrefix mu e = 0 := by
  by_cases hm : mu = 0
  · simp [hm, relativePrefix]
  have hl := (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hm).mp h
  have hf : (Ordinal.CNF Ordinal.omega0 mu).filter (fun p => e ≤ p.1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have he := (Ordinal.CNF.fst_le_log hp).trans_lt hl
    simpa using not_le_of_gt he
  simp [relativePrefix, hf]

private theorem raw_absorption (a : ONote) (ha : ONote.NF a) (y : Ordinal.{0}) (hy : y ≠ 0) :
    a.repr + y = relativePrefix a.repr (Ordinal.log Ordinal.omega0 y) + y := by
  induction a with
  | zero => simp [ONote.repr, relativePrefix]
  | oadd f c t ihf iht =>
    let e := Ordinal.log Ordinal.omega0 y
    have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
    have hcnf : Ordinal.CNF Ordinal.omega0 (ONote.oadd f c t).repr =
        (f.repr, ((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr :=
      Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc
        (Ordinal.natCast_lt_omega0 _) ha.snd'.repr_lt
    by_cases he : e ≤ f.repr
    · have hp : relativePrefix (ONote.oadd f c t).repr e =
          Ordinal.omega0 ^ f.repr * (c : Nat) + relativePrefix t.repr e := by
        simp only [relativePrefix, hcnf]
        simp [he]
      change (Ordinal.omega0 ^ f.repr * (c : Nat) + t.repr) + y =
        relativePrefix (ONote.oadd f c t).repr e + y
      rw [hp, add_assoc, add_assoc, iht ha.snd]
    · have hfe : f.repr < e := lt_of_not_ge he
      have hsmall : (ONote.oadd f c t).repr < Ordinal.omega0 ^ e :=
        (ha.below_of_lt hfe).repr_lt
      rw [prefix_zero_of_small _ _ hsmall, zero_add]
      exact Ordinal.add_of_omega0_opow_le hsmall (Ordinal.opow_log_le_self _ hy)

 theorem relativeNorm : Targets.RelativeNorm := by
  intro mu y hmu hy
  by_cases hy0 : y = 0
  · subst y
    have hz : actualOrdinalNorm 0 = 0 := by
      simpa [ONote.repr, Vendor.R1.treeWeight] using
        actualOrdinalNorm_notationCorrespondence (⟨0, inferInstance⟩ : NONote)
    simp [relativeCost, hz]
  let e := Ordinal.log Ordinal.omega0 y
  have hp := relativePrefixNorm mu e hmu
  have habs : mu + y = relativePrefix mu e + y := by
    obtain ⟨a, rfl⟩ := normalRepresentationComplete mu hmu
    exact raw_absorption a.1 a.2 y hy0
  have hmin : actualMinExponentAtLeast (relativePrefix mu e) e := by
    intro p hmem
    rw [relativePrefix_cnf mu e hmu] at hmem
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  have hd := (actualMinExponentDivisibility _ hp.1 e).mp hmin
  have hbound : y < Ordinal.omega0 ^ (e+1) :=
    Ordinal.lt_opow_of_log_lt Ordinal.one_lt_omega0 (Order.lt_add_one_iff.mpr le_rfl)
  have hn := (actualDivisiblePrefixNormAddition _ _ hp.1 hy e hd hbound).2
  refine ⟨?_, Nat.zero_le _, ?_⟩
  · rw [habs, hn]
    simp [relativeCost, hy0, relativeProfile, e, Nat.add_comm]
  · simpa [relativeCost, hy0, e] using hp.2.2

end LogicLineages.PermittedControl
