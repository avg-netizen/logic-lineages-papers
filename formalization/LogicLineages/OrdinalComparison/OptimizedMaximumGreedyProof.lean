module
public import LogicLineages.OrdinalComparison.OptimizedMaximumBaseProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- A literal normal CNF block has its source norm and remains below epsilon zero. -/
theorem actualCNFBlock (e r : Ordinal) (he : e < epsilonZero)
    (hr : r < Ordinal.omega0 ^ e) (c : PNat) :
    Ordinal.omega0 ^ e * ((c : Nat) : Ordinal) + r < epsilonZero ∧
      actualOrdinalNorm (Ordinal.omega0 ^ e * ((c : Nat) : Ordinal) + r) =
        (c : Nat) * (1 + actualOrdinalNorm e) + actualOrdinalNorm r ∧
      ∀ d : Ordinal, e < d →
        Ordinal.omega0 ^ e * ((c : Nat) : Ordinal) + r < Ordinal.omega0 ^ d := by
  obtain ⟨en, hen⟩ := normalRepresentationComplete e he
  have hpow : Ordinal.omega0 ^ e < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr he
  obtain ⟨rn, hrn⟩ := normalRepresentationComplete r (hr.trans hpow)
  have htail : ONote.NFBelow rn.1 en.1.repr :=
    ONote.NF.below_of_lt' (by rw [hen, hrn]; exact hr) rn.2
  let node : NONote := ⟨ONote.oadd en.1 c rn.1, en.2.oadd c htail⟩
  have hrepr : node.1.repr = Ordinal.omega0 ^ e * ((c : Nat) : Ordinal) + r := by
    simp only [node, ONote.repr, hen, hrn]
  have hne := actualOrdinalNorm_notationCorrespondence en
  have hnr := actualOrdinalNorm_notationCorrespondence rn
  rw [hen] at hne
  rw [hrn] at hnr
  refine ⟨by rw [← hrepr]; exact normalRepresentationSound node, ?_, ?_⟩
  · rw [← hrepr, actualOrdinalNorm_notationCorrespondence node]
    change (c : Nat) * (1 + Vendor.R1.treeWeight en.1) + Vendor.R1.treeWeight rn.1 = _
    rw [← hne, ← hnr]
  · intro d hd
    rw [← hrepr]
    exact (ONote.NF.below_of_lt (by rw [hen]; exact hd) node.2).repr_lt

/-- The source lower-power greedy clause, against the independent finite maximum. -/
theorem actualLowerPowerGreedyRecurrence : Targets.ActualLowerPowerGreedyRecurrence := by
  intro e hepos he b hb
  dsimp only
  let a := actualMaximumPredecessor e (b - 1)
  let v := 1 + actualOrdinalNorm a
  let q := b / v
  let s := b % v
  have ha := actualMaximumPredecessor_correct e hepos he (b - 1)
  have haeps : a < epsilonZero := ha.1.1.trans he
  have hvpos : 0 < v := by dsimp [v]; omega
  have hv : v ≤ b := by dsimp [v, a]; have := ha.1.2; omega
  have hq : 0 < q := Nat.div_pos hv hvpos
  let qp : PNat := ⟨q, hq⟩
  have hpoweps : Ordinal.omega0 ^ a < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr haeps
  have ht := actualMaximumPredecessor_correct (Ordinal.omega0 ^ a)
    (Ordinal.opow_pos _ Ordinal.omega0_pos) hpoweps s
  let t := actualLowerPowerMaximum a s
  have htlt : t < Ordinal.omega0 ^ a := ht.1.1
  have htbudget : actualOrdinalNorm t ≤ s := ht.1.2
  have hblock := actualCNFBlock a t haeps htlt qp
  let z := Ordinal.omega0 ^ a * (q : Ordinal) + t
  have hzbound : z < Ordinal.omega0 ^ e := hblock.2.2 e ha.1.1
  have hdiv : q * v + s = b := by
    dsimp [q, s]
    simpa only [Nat.mul_comm] using Nat.div_add_mod b v
  have hzbudget : actualOrdinalNorm z ≤ b := by
    have hnorm := hblock.2.1
    change actualOrdinalNorm z = q * v + actualOrdinalNorm t at hnorm
    rw [hnorm]
    omega
  have hgreatest : IsGreatest {x : Ordinal | x < Ordinal.omega0 ^ e ∧ actualOrdinalNorm x ≤ b} z := by
    refine ⟨⟨hzbound, hzbudget⟩, ?_⟩
    intro x hx
    have hxb : actualOrdinalNorm x ≤ b := hx.2
    have hxe : x < epsilonZero := hx.1.trans
      ((Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr he)
    obtain ⟨xn, hxn⟩ := normalRepresentationComplete x hxe
    rcases xn with ⟨raw, hnf⟩
    cases raw with
    | zero =>
      have hxzero : x = 0 := hxn.symm
      rw [hxzero]
      exact zero_le
    | oadd f c r =>
      have hf : f.repr < e := (ONote.NF.below_of_lt' (by rw [hxn]; exact hx.1) hnf).lt
      have hfnorm := actualOrdinalNorm_notationCorrespondence (⟨f, hnf.fst⟩ : NONote)
      change actualOrdinalNorm f.repr = Vendor.R1.treeWeight f at hfnorm
      have hrnorm := actualOrdinalNorm_notationCorrespondence (⟨r, hnf.snd⟩ : NONote)
      change actualOrdinalNorm r.repr = Vendor.R1.treeWeight r at hrnorm
      have hxnorm := actualOrdinalNorm_notationCorrespondence
        (⟨ONote.oadd f c r, hnf⟩ : NONote)
      change actualOrdinalNorm (ONote.oadd f c r).repr =
        (c : Nat) * (1 + Vendor.R1.treeWeight f) + Vendor.R1.treeWeight r at hxnorm
      rw [← hfnorm, ← hrnorm, hxn] at hxnorm
      change actualOrdinalNorm x =
        (c : Nat) * (1 + actualOrdinalNorm f.repr) + actualOrdinalNorm r.repr at hxnorm
      have hcharge : (c : Nat) * (1 + actualOrdinalNorm f.repr) ≤ b := by omega
      have hfc : actualOrdinalNorm f.repr ≤ b - 1 := by
        have hc := c.pos
        have hmul : 1 + actualOrdinalNorm f.repr ≤
            (c : Nat) * (1 + actualOrdinalNorm f.repr) := by
          simpa only [Nat.one_mul] using Nat.mul_le_mul_right
            (1 + actualOrdinalNorm f.repr) (Nat.one_le_iff_ne_zero.mpr c.ne_zero)
        omega
      have hfa : f.repr ≤ a := ha.2 ⟨hf, hfc⟩
      by_cases hstrict : f.repr < a
      · have hxbelow : x < Ordinal.omega0 ^ a := by
          rw [← hxn]
          exact (hnf.below_of_lt hstrict).repr_lt
        have hωz : Ordinal.omega0 ^ a ≤ z := by
          have hn : (1 : Ordinal) ≤ (q : Ordinal) := by exact_mod_cast hq
          have hm := mul_le_mul_left' hn (Ordinal.omega0 ^ a)
          simpa only [mul_one] using hm.trans (le_self_add :
            Ordinal.omega0 ^ a * (q : Ordinal) ≤ z)
        exact (hxbelow.trans_le hωz).le
      · have hfeq : f.repr = a := le_antisymm hfa (le_of_not_gt hstrict)
        have hcq : (c : Nat) ≤ q := by
          apply (Nat.le_div_iff_mul_le hvpos).mpr
          simpa only [v, hfeq] using hcharge
        by_cases hcstrict : (c : Nat) < q
        · have htail : r.repr < Ordinal.omega0 ^ a := by
            simpa only [hfeq] using hnf.snd'.repr_lt
          have hxnext : x < Ordinal.omega0 ^ a * ((c : Nat) : Ordinal) + Ordinal.omega0 ^ a := by
            rw [← hxn]
            change Ordinal.omega0 ^ f.repr * ((c : Nat) : Ordinal) + r.repr < _
            rw [hfeq]
            exact add_lt_add_right htail _
          have hcoeff : ((c : Nat) : Ordinal) + 1 ≤ (q : Ordinal) := by exact_mod_cast hcstrict
          have hnext : Ordinal.omega0 ^ a * ((c : Nat) : Ordinal) + Ordinal.omega0 ^ a ≤
              Ordinal.omega0 ^ a * (q : Ordinal) := by
            rw [← mul_add_one]
            exact mul_le_mul_left' hcoeff _
          exact (hxnext.trans_le (hnext.trans le_self_add)).le
        · have hceq : (c : Nat) = q := by omega
          have hrt : r.repr ≤ t := by
            apply ht.2
            refine ⟨by simpa only [hfeq] using hnf.snd'.repr_lt, ?_⟩
            rw [hfeq, hceq] at hxnorm
            change actualOrdinalNorm x = q * v + actualOrdinalNorm r.repr at hxnorm
            omega
          rw [← hxn]
          change Ordinal.omega0 ^ f.repr * ((c : Nat) : Ordinal) + r.repr ≤ z
          rw [hfeq, hceq]
          exact add_le_add_right hrt _
  exact (actualMaximumPredecessor_unique _ (Ordinal.opow_pos _ Ordinal.omega0_pos)
    ((Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr he) b z hgreatest).symm

end LogicLineages.OrdinalComparison
