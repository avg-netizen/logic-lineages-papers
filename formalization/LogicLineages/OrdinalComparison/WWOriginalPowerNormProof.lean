module
public import LogicLineages.OrdinalComparison.WWOriginalPowerNormTargets
public import LogicLineages.OrdinalComparison.ActualCollapseBounds

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open Vendor.R1

private theorem one_add_weight (a : ONote) :
    treeWeight a ≤ treeWeight ((1 : ONote) + a) ∧
    treeWeight ((1 : ONote) + a) ≤ 1 + treeWeight a := by
  change treeWeight a ≤ treeWeight (ONote.add (.oadd .zero 1 .zero) a) ∧
    treeWeight (ONote.add (.oadd .zero 1 .zero) a) ≤ 1 + treeWeight a
  cases a with
  | zero => simp [ONote.add, ONote.addAux, treeWeight]
  | oadd e c t =>
    cases e with
    | zero => simp [ONote.add, ONote.addAux, ONote.cmp, treeWeight, PNat.add_coe]; omega
    | oadd f d u => simp [ONote.add, ONote.addAux, ONote.cmp, treeWeight]

private theorem scale_weight (a : ONote) :
    treeWeight a ≤ treeWeight (ONote.scale 1 a) ∧
    treeWeight (ONote.scale 1 a) ≤ 2 * treeWeight a := by
  induction a with
  | zero => simp [ONote.scale, treeWeight]
  | oadd e c t ihe iht =>
    have he := one_add_weight e
    have hlo := Nat.mul_le_mul_left (c : Nat) (Nat.add_le_add_left he.1 1)
    have hhi : (c : Nat) * (1 + treeWeight ((1 : ONote) + e)) ≤
        2 * ((c : Nat) * (1 + treeWeight e)) := by
      calc
        _ ≤ (c : Nat) * (2 * (1 + treeWeight e)) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ac_rfl
    simp only [ONote.scale, treeWeight]
    constructor
    · exact Nat.add_le_add hlo iht.1
    · simpa only [Nat.mul_add] using Nat.add_le_add hhi iht.2

private theorem scaled_note (x : NONote) :
    ∃ y : NONote, y.1.repr = Ordinal.omega0 * x.1.repr ∧
      treeWeight y.1 = treeWeight (ONote.scale 1 x.1) := by
  letI : ONote.NF x.1 := x.2
  refine ⟨⟨ONote.scale 1 x.1, inferInstance⟩, ?_, rfl⟩
  simp only [ONote.repr_scale, ONote.repr_one, Nat.cast_one, Ordinal.opow_one]

theorem actualOmegaLeftNormBounds : Targets.ActualOmegaLeftNormBounds := by
  intro a ha
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy, hw⟩ := scaled_note x
  rw [← hx, ← hy, actualOrdinalNorm_notationCorrespondence x,
    actualOrdinalNorm_notationCorrespondence y, hw]
  exact scale_weight x.1

theorem actualBaseTwoPowerNormFormula : Targets.ActualBaseTwoPowerNormFormula := by
  intro a ha k
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  let c : ℕ+ := ⟨2 ^ k, Nat.pow_pos (by omega)⟩
  let y : NONote := ⟨.oadd x.1 c .zero, ONote.NF.oadd x.2 c ONote.NFBelow.zero⟩
  have hy : y.1.repr = Ordinal.omega0 ^ a * ((2 ^ k : Nat) : Ordinal) := by
    simp only [y, ONote.repr, hx, c, Nat.cast_zero, add_zero]
    rfl
  have he : (2 : Ordinal) ^ (Ordinal.omega0 * a + (k : Ordinal)) =
      Ordinal.omega0 ^ a * ((2 ^ k : Nat) : Ordinal) := by
    rw [Ordinal.opow_add, Ordinal.opow_mul,
      Ordinal.opow_omega0 (a := (2 : Ordinal))
        (by exact_mod_cast (show (1 : Nat) < 2 by omega))
        (by simpa using Ordinal.natCast_lt_omega0 2)]
    congr 1
    simpa only [Ordinal.opow_natCast, Nat.cast_ofNat] using (Ordinal.natCast_pow 2 k).symm
  rw [he, ← hy, actualOrdinalNorm_notationCorrespondence y,
    ← hx, actualOrdinalNorm_notationCorrespondence x]
  simp only [y, treeWeight, c, Nat.add_zero]
  rfl

private theorem omega_split_norm (a : Ordinal) (ha : a < epsilonZero) :
    ∃ b : Ordinal, ∃ k : Nat, b < epsilonZero ∧ a = Ordinal.omega0 * b + (k : Ordinal) ∧
      actualOrdinalNorm a = actualOrdinalNorm (Ordinal.omega0 * b) + k := by
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  letI : ONote.NF x.1 := x.2
  rcases hspl : ONote.split' x.1 with ⟨b, k⟩
  have hs := ONote.nf_repr_split' hspl
  let y : NONote := ⟨b, hs.1⟩
  obtain ⟨z, hz, hw⟩ := scaled_note y
  have hzb : Ordinal.omega0 * b.repr < epsilonZero := by
    rw [← hz]
    exact normalRepresentationSound z
  have hn := actualFiniteTailClosureNorm _ hzb k
  refine ⟨b.repr, k, normalRepresentationSound y, ?_, ?_⟩
  · exact hx.symm.trans hs.2
  · rw [hx.symm.trans hs.2]
    exact hn.2

theorem actualBaseTwoInverseNorm : Targets.ActualBaseTwoInverseNorm := by
  intro a ha
  obtain ⟨b, k, hb, he, hn⟩ := omega_split_norm a ha
  have hscale := (actualOmegaLeftNormBounds b hb).2
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have hk : k ≤ 2 ^ k := (show k < 2 ^ k from Nat.lt_two_pow_self).le
  have hm : actualOrdinalNorm b ≤ 2 ^ k * actualOrdinalNorm b := by
    simpa using Nat.mul_le_mul_right (actualOrdinalNorm b) hpow
  rw [he, actualBaseTwoPowerNormFormula b hb k]
  have hna : actualOrdinalNorm (Ordinal.omega0 * b + (k : Ordinal)) ≤
      2 * actualOrdinalNorm b + k := by
    rw [← he]
    omega
  calc
    _ ≤ 2 * actualOrdinalNorm b + k := hna
    _ ≤ 2 * (2 ^ k * actualOrdinalNorm b) + 2 ^ k :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 hm) hk
    _ ≤ 2 * (2 ^ k * (1 + actualOrdinalNorm b)) := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega

theorem actualBaseTwoForwardNorm : Targets.ActualBaseTwoForwardNorm := by
  intro a ha
  obtain ⟨b, k, hb, he, hn⟩ := omega_split_norm a ha
  have hscale := (actualOmegaLeftNormBounds b hb).1
  have hexp : k + actualOrdinalNorm b ≤ actualOrdinalNorm a := by omega
  have hsmall : 1 + actualOrdinalNorm b ≤ 2 ^ actualOrdinalNorm b := by
    have : actualOrdinalNorm b < 2 ^ actualOrdinalNorm b := Nat.lt_two_pow_self
    omega
  rw [he, actualBaseTwoPowerNormFormula b hb k]
  calc
    _ ≤ 2 ^ k * 2 ^ actualOrdinalNorm b := Nat.mul_le_mul_left _ hsmall
    _ = 2 ^ (k + actualOrdinalNorm b) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ actualOrdinalNorm (Ordinal.omega0 * b + (k : Ordinal)) := by
      apply Nat.pow_le_pow_right (by omega)
      rwa [← he]

end LogicLineages.OrdinalComparison.Source.OriginalDomain
