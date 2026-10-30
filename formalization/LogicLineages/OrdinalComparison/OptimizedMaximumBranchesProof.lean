module
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- The two first lexicographic CNF restrictions, on literal ordinal blocks. -/
private theorem cnf_leading_restrictions (e r f s : Ordinal)
    (hr : r < Ordinal.omega0 ^ e) (hs : s < Ordinal.omega0 ^ f) (c d : PNat)
    (hlt : Ordinal.omega0 ^ f * ((d : Nat) : Ordinal) + s <
      Ordinal.omega0 ^ e * ((c : Nat) : Ordinal) + r) :
    f ≤ e ∧ (f = e → (d : Nat) ≤ (c : Nat) ∧ ((d : Nat) = (c : Nat) → s < r)) := by
  have hf : f ≤ e := by
    by_contra hn
    have hef : e < f := lt_of_not_ge hn
    have hleft : Ordinal.omega0 ^ e * ((c : Nat) : Ordinal) + r < Ordinal.omega0 ^ f :=
      Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 _) hr hef
    have hright : Ordinal.omega0 ^ f ≤ Ordinal.omega0 ^ f * ((d : Nat) : Ordinal) + s :=
      (Ordinal.le_mul_left _ (by exact_mod_cast d.pos)).trans le_self_add
    exact (not_lt_of_ge hright) (hlt.trans hleft)
  refine ⟨hf, ?_⟩
  intro hfe
  subst f
  have hdc : (d : Nat) ≤ (c : Nat) := by
    by_contra hn
    have hcd : (c : Nat) < (d : Nat) := Nat.lt_of_not_ge hn
    have hx : Ordinal.omega0 ^ e * ((c : Nat) : Ordinal) + r <
        Ordinal.omega0 ^ e * ((d : Nat) : Ordinal) :=
      Ordinal.opow_mul_add_lt_opow_mul hr (by exact_mod_cast hcd)
    exact (not_lt_of_ge le_self_add) (hlt.trans hx)
  refine ⟨hdc, ?_⟩
  intro hde
  rw [hde] at hlt
  exact (add_lt_add_iff_left _).mp hlt

private theorem actual_block_positive (e r : Ordinal) (c : PNat) :
    0 < Ordinal.omega0 ^ e * ((c : Nat) : Ordinal) + r :=
  Ordinal.opow_mul_add_pos (ne_of_gt Ordinal.omega0_pos) e
    (by exact_mod_cast c.ne_zero) r

theorem actualMaximumRetainLeadingBlock : Targets.ActualMaximumRetainLeadingBlock := by
  intro e r he hr hrpos c hc b hbudget
  let cp : PNat := ⟨c, hc⟩
  let w := 1 + actualOrdinalNorm e
  let m := actualMaximumPredecessor r (b - c * w)
  have hsource := actualCNFBlock e r he hr cp
  have hrε : r < epsilonZero := hr.trans
    ((Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr he)
  have hm := actualMaximumPredecessor_correct r hrpos hrε (b - c * w)
  have hmω : m < Ordinal.omega0 ^ e := hm.1.1.trans hr
  have hout := actualCNFBlock e m he hmω cp
  let z := Ordinal.omega0 ^ e * (c : Ordinal) + m
  have hzlt : z < Ordinal.omega0 ^ e * (c : Ordinal) + r := add_lt_add_right hm.1.1 _
  have hzbudget : actualOrdinalNorm z ≤ b := by
    have hn := hout.2.1
    change actualOrdinalNorm z = c * w + actualOrdinalNorm m at hn
    have hmb : actualOrdinalNorm m ≤ b - c * w := hm.1.2
    change c * w ≤ b at hbudget
    omega
  apply Eq.symm
  apply actualMaximumPredecessor_unique _ (actual_block_positive e r cp) hsource.1 b z
  refine ⟨⟨hzlt, hzbudget⟩, ?_⟩
  intro x hx
  have hxb : actualOrdinalNorm x ≤ b := hx.2
  obtain ⟨xn, hxn⟩ := normalRepresentationComplete x (hx.1.trans hsource.1)
  rcases xn with ⟨raw, hnf⟩
  cases raw with
  | zero =>
    have hxzero : x = 0 := hxn.symm
    rw [hxzero]
    exact zero_le
  | oadd f d s =>
    have hrepr : Ordinal.omega0 ^ f.repr * ((d : Nat) : Ordinal) + s.repr = x := hxn
    have hrestr := cnf_leading_restrictions e r f.repr s.repr hr hnf.snd'.repr_lt cp d
      (hrepr ▸ hx.1)
    by_cases hfe : f.repr < e
    · have hxω : x < Ordinal.omega0 ^ e := by
        rw [← hrepr]
        exact Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 _) hnf.snd'.repr_lt hfe
      have hωz : Ordinal.omega0 ^ e ≤ z :=
        (Ordinal.le_mul_left _ (by exact_mod_cast hc)).trans le_self_add
      exact (hxω.trans_le hωz).le
    · have hfeq : f.repr = e := le_antisymm hrestr.1 (le_of_not_gt hfe)
      have hcoeff := hrestr.2 hfeq
      by_cases hdc : (d : Nat) < c
      · have hxprefix : x < Ordinal.omega0 ^ e * (c : Ordinal) := by
          rw [← hrepr, hfeq]
          exact Ordinal.opow_mul_add_lt_opow_mul
            (by simpa only [hfeq] using hnf.snd'.repr_lt) (by exact_mod_cast hdc)
        exact (hxprefix.trans_le le_self_add).le
      · have hdeq : (d : Nat) = c := by have := hcoeff.1; change (d : Nat) ≤ c at this; omega
        have hslt : s.repr < r := hcoeff.2 hdeq
        have hsbudget : actualOrdinalNorm s.repr ≤ b - c * w := by
          have hn := actualOrdinalNorm_notationCorrespondence (⟨ONote.oadd f d s, hnf⟩ : NONote)
          have hfn := actualOrdinalNorm_notationCorrespondence (⟨f, hnf.fst⟩ : NONote)
          have hsn := actualOrdinalNorm_notationCorrespondence (⟨s, hnf.snd⟩ : NONote)
          change actualOrdinalNorm f.repr = Vendor.R1.treeWeight f at hfn
          change actualOrdinalNorm s.repr = Vendor.R1.treeWeight s at hsn
          change actualOrdinalNorm (ONote.oadd f d s).repr =
            (d : Nat) * (1 + Vendor.R1.treeWeight f) + Vendor.R1.treeWeight s at hn
          rw [← hfn, ← hsn, hxn, hfeq, hdeq] at hn
          change actualOrdinalNorm x = c * w + actualOrdinalNorm s.repr at hn
          omega
        have hsm : s.repr ≤ m := hm.2 ⟨hslt, hsbudget⟩
        rw [← hrepr, hfeq, hdeq]
        exact add_le_add_right hsm _

theorem actualMaximumDropLeadingBlock : Targets.ActualMaximumDropLeadingBlock := by
  classical
  intro e r he hr c hc b hnot
  dsimp only
  let w := 1 + actualOrdinalNorm e
  let d := actualMaximumDropCoefficient e r c b
  have hw : 0 < w := by dsimp [w]; omega
  have hdaff : d ≤ b / w := by
    dsimp [d, actualMaximumDropCoefficient, w]
    exact min_le_right _ _
  have hdc : d < c := by
    by_cases hrzero : r = 0
    · dsimp [d, actualMaximumDropCoefficient]
      rw [if_pos hrzero]
      have hd := min_le_left (c - 1) (b / (1 + actualOrdinalNorm e))
      omega
    · have hpositive : 0 < r := pos_iff_ne_zero.mpr hrzero
      have hbudget : ¬c * w ≤ b := fun h => hnot ⟨hpositive, h⟩
      have hdiv : b / w < c := (Nat.div_lt_iff_lt_mul hw).mpr (by omega)
      exact hdaff.trans_lt hdiv
  have hdcharge : d * w ≤ b := (Nat.le_div_iff_mul_le hw).mp hdaff
  have hpowε : Ordinal.omega0 ^ e < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr he
  let m := actualLowerPowerMaximum e (b - d * w)
  have hm := actualMaximumPredecessor_correct (Ordinal.omega0 ^ e)
    (Ordinal.opow_pos _ Ordinal.omega0_pos) hpowε (b - d * w)
  have hmω : m < Ordinal.omega0 ^ e := hm.1.1
  let z := Ordinal.omega0 ^ e * (d : Ordinal) + m
  have hzlt : z < Ordinal.omega0 ^ e * (c : Ordinal) + r :=
    (Ordinal.opow_mul_add_lt_opow_mul hmω (by exact_mod_cast hdc)).trans_le le_self_add
  have hzbudget : actualOrdinalNorm z ≤ b := by
    by_cases hd : d = 0
    · have hz : z = m := by simp only [z, hd, Nat.cast_zero, mul_zero, zero_add]
      rw [hz]
      have hmb : actualOrdinalNorm m ≤ b - d * w := hm.1.2
      omega
    · have hout := actualCNFBlock e m he hmω (⟨d, Nat.pos_of_ne_zero hd⟩ : PNat)
      have hn := hout.2.1
      change actualOrdinalNorm z = d * w + actualOrdinalNorm m at hn
      have hmb : actualOrdinalNorm m ≤ b - d * w := hm.1.2
      omega
  have hsource := actualCNFBlock e r he hr (⟨c, hc⟩ : PNat)
  apply Eq.symm
  apply actualMaximumPredecessor_unique _ (actual_block_positive e r ⟨c, hc⟩) hsource.1 b z
  refine ⟨⟨hzlt, hzbudget⟩, ?_⟩
  intro x hx
  have hxb : actualOrdinalNorm x ≤ b := hx.2
  obtain ⟨xn, hxn⟩ := normalRepresentationComplete x (hx.1.trans hsource.1)
  rcases xn with ⟨raw, hnf⟩
  cases raw with
  | zero =>
    have hxzero : x = 0 := hxn.symm
    rw [hxzero]
    exact zero_le
  | oadd f k s =>
    have hrepr : Ordinal.omega0 ^ f.repr * ((k : Nat) : Ordinal) + s.repr = x := hxn
    have hrestr := cnf_leading_restrictions e r f.repr s.repr hr hnf.snd'.repr_lt ⟨c, hc⟩ k
      (hrepr ▸ hx.1)
    by_cases hfe : f.repr < e
    · have hxω : x < Ordinal.omega0 ^ e := by
        rw [← hrepr]
        exact Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 _) hnf.snd'.repr_lt hfe
      by_cases hd : d = 0
      · have hxm : x ≤ m := hm.2 ⟨hxω, by simpa only [hd, Nat.zero_mul, Nat.sub_zero] using hxb⟩
        simpa only [z, hd, Nat.cast_zero, mul_zero, zero_add] using hxm
      · have hωz : Ordinal.omega0 ^ e ≤ z :=
          (Ordinal.le_mul_left _ (by exact_mod_cast Nat.pos_of_ne_zero hd)).trans le_self_add
        exact (hxω.trans_le hωz).le
    · have hfeq : f.repr = e := le_antisymm hrestr.1 (le_of_not_gt hfe)
      have hcoeff := hrestr.2 hfeq
      have hxnorm : actualOrdinalNorm x = (k : Nat) * w + actualOrdinalNorm s.repr := by
        have hn := actualOrdinalNorm_notationCorrespondence (⟨ONote.oadd f k s, hnf⟩ : NONote)
        have hfn := actualOrdinalNorm_notationCorrespondence (⟨f, hnf.fst⟩ : NONote)
        have hsn := actualOrdinalNorm_notationCorrespondence (⟨s, hnf.snd⟩ : NONote)
        change actualOrdinalNorm f.repr = Vendor.R1.treeWeight f at hfn
        change actualOrdinalNorm s.repr = Vendor.R1.treeWeight s at hsn
        change actualOrdinalNorm (ONote.oadd f k s).repr =
          (k : Nat) * (1 + Vendor.R1.treeWeight f) + Vendor.R1.treeWeight s at hn
        rw [← hfn, ← hsn, hxn, hfeq] at hn
        exact hn
      have hkaff : (k : Nat) ≤ b / w := (Nat.le_div_iff_mul_le hw).mpr (by omega)
      have hkd : (k : Nat) ≤ d := by
        dsimp [d, actualMaximumDropCoefficient]
        apply le_min _ hkaff
        split_ifs with hrzero
        · have hklt : (k : Nat) < c := by
            have hle := hcoeff.1
            change (k : Nat) ≤ c at hle
            by_contra hn
            have heq : (k : Nat) = c := by omega
            have hslt := hcoeff.2 heq
            rw [hrzero] at hslt
            exact (not_lt_of_ge zero_le) hslt
          omega
        · exact hcoeff.1
      by_cases hkstrict : (k : Nat) < d
      · have hxprefix : x < Ordinal.omega0 ^ e * (d : Ordinal) := by
          rw [← hrepr, hfeq]
          exact Ordinal.opow_mul_add_lt_opow_mul
            (by simpa only [hfeq] using hnf.snd'.repr_lt) (by exact_mod_cast hkstrict)
        exact (hxprefix.trans_le le_self_add).le
      · have hkeq : (k : Nat) = d := by omega
        have hsm : s.repr ≤ m := by
          apply hm.2
          refine ⟨by simpa only [hfeq] using hnf.snd'.repr_lt, ?_⟩
          rw [hkeq] at hxnorm
          omega
        rw [← hrepr, hfeq, hkeq]
        exact add_le_add_right hsm _

theorem actualOptimizedMaximumRecurrences : Targets.ActualOptimizedMaximumRecurrences :=
  ⟨actualOptimizedMaximumBaseCases, actualMaximumRetainLeadingBlock,
    actualMaximumDropLeadingBlock, actualLowerPowerGreedyRecurrence, optimizedMaximumCallsDecrease⟩

end LogicLineages.OrdinalComparison
