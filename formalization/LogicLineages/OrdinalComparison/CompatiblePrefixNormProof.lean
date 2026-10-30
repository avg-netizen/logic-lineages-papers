module
public import LogicLineages.OrdinalComparison.CompatiblePrefixFactsProof
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem note_cmp_gt (a b : ONote) (ha : ONote.NF a) (hb : ONote.NF b)
    (h : b.repr < a.repr) : ONote.cmp a b = .gt :=
  (@ONote.cmp_compares a b ha hb).eq_gt.mpr h

private theorem note_cmp_self (a : ONote) (ha : ONote.NF a) : ONote.cmp a a = .eq :=
  (@ONote.cmp_compares a a ha ha).eq_eq.mpr rfl

private theorem addAux_norm_below (f : ONote) (hf : ONote.NF f) (c : PNat)
    (r : ONote) (hr : ONote.NFBelow r f.repr) :
    Vendor.R1.treeWeight (ONote.addAux f c r) =
      (c : Nat) * (1 + Vendor.R1.treeWeight f) + Vendor.R1.treeWeight r := by
  cases r with
  | zero => simp [ONote.addAux, Vendor.R1.treeWeight]
  | oadd g d s =>
    have hcmp := note_cmp_gt f g hf hr.fst hr.lt
    simp only [ONote.addAux, hcmp, Vendor.R1.treeWeight]

private theorem raw_divisible_prefix_norm (b : ONote) (hb : ONote.NF b) (e : Ordinal)
    (hbound : b.repr < Ordinal.omega0 ^ (e + 1)) :
    ∀ a : ONote, ONote.NF a → Ordinal.omega0 ^ e ∣ a.repr →
      Vendor.R1.treeWeight (a + b) = Vendor.R1.treeWeight a + Vendor.R1.treeWeight b := by
  intro a
  induction a with
  | zero =>
    intro _ _
    change Vendor.R1.treeWeight b = 0 + Vendor.R1.treeWeight b
    simp only [Nat.zero_add]
  | oadd f c t ihf iht =>
    intro ha hdvd
    have hd := ha.of_dvd_omega0_opow hdvd
    by_cases hstrict : e < f.repr
    · have hrbelow : ONote.NFBelow b f.repr :=
        ONote.NF.below_of_lt' (hbound.trans_le
          ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone (Order.add_one_le_of_lt hstrict))) hb
      have hsum := ONote.add_nfBelow ha.snd' hrbelow
      rw [ONote.oadd_add, addAux_norm_below f ha.fst c (t + b) hsum, iht ha.snd hd.2]
      simp only [Vendor.R1.treeWeight, Nat.add_assoc]
    · have heq : f.repr = e := le_antisymm (le_of_not_gt hstrict) hd.1
      have htzero : t = 0 := by
        by_contra htne
        have hrne : t.repr ≠ 0 := by
          intro hz
          letI := ha.snd
          exact htne (ONote.repr_inj.mp hz)
        have hle := Ordinal.le_of_dvd hrne hd.2
        have hlt : t.repr < Ordinal.omega0 ^ e := by rw [← heq]; exact ha.snd'.repr_lt
        exact (not_lt_of_ge hle) hlt
      subst t
      cases b with
      | zero => simp [ONote.oadd_add, ONote.addAux, Vendor.R1.treeWeight]
      | oadd g d r =>
        have hg : g.repr ≤ e :=
          Order.lt_add_one_iff.mp (ONote.NF.below_of_lt' hbound hb).lt
        by_cases hgt : g.repr < e
        · have hcmp := note_cmp_gt f g ha.fst hb.fst (by rw [heq]; exact hgt)
          simp only [ONote.oadd_add, ONote.zero_add, ONote.addAux, hcmp, Vendor.R1.treeWeight,
            Nat.add_zero]
        · have hgeq : g.repr = e := le_antisymm hg (le_of_not_gt hgt)
          letI := ha.fst
          letI := hb.fst
          have hfg : f = g := ONote.repr_inj.mp (heq.trans hgeq.symm)
          subst g
          have hcmp := note_cmp_self f ha.fst
          simp only [ONote.oadd_add, ONote.zero_add, ONote.addAux, hcmp, Vendor.R1.treeWeight,
            PNat.add_coe, Nat.add_mul, Nat.add_assoc, Nat.add_zero]

theorem rawDivisiblePrefixNormAddition : Targets.RawDivisiblePrefixNormAddition := by
  intro a b e hd hb
  exact raw_divisible_prefix_norm b.1 b.2 e hb a.1 a.2 hd

theorem actualDivisiblePrefixNormAddition : Targets.ActualDivisiblePrefixNormAddition := by
  intro k r hk hr e hd hbound
  obtain ⟨kn, hkn⟩ := normalRepresentationComplete k hk
  obtain ⟨rn, hrn⟩ := normalRepresentationComplete r hr
  letI := kn.2
  letI := rn.2
  let out : NONote := ⟨kn.1 + rn.1, inferInstance⟩
  have hrepr : out.1.repr = k + r := by
    change (kn.1 + rn.1).repr = k + r
    rw [ONote.repr_add, hkn, hrn]
  have hnorm := rawDivisiblePrefixNormAddition kn rn e
    (by rw [hkn]; exact hd) (by rw [hrn]; exact hbound)
  have hnk := actualOrdinalNorm_notationCorrespondence kn
  have hnr := actualOrdinalNorm_notationCorrespondence rn
  rw [hkn] at hnk
  rw [hrn] at hnr
  refine ⟨by rw [← hrepr]; exact normalRepresentationSound out, ?_⟩
  rw [← hrepr, actualOrdinalNorm_notationCorrespondence out]
  change Vendor.R1.treeWeight (kn.1 + rn.1) = _
  rw [hnorm, ← hnk, ← hnr]

end LogicLineages.OrdinalComparison
