module
public import LogicLineages.OrdinalComparison.WWOriginalProductLowerTargets
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open Vendor.R1

private theorem weight_positive {a : ONote} (ha : a ≠ .zero) : 0 < treeWeight a := by
  cases a with
  | zero => exact False.elim (ha rfl)
  | oadd e c t =>
    have hp : 0 < (c : Nat) * (1 + treeWeight e) := Nat.mul_pos c.pos (by omega)
    simp only [treeWeight]
    omega

private theorem paired_lower (c d a b : Nat) (hc : 0 < c) (hd : 0 < d) :
    c * (1 + a) + d * (1 + b) ≤ c * d * (1 + (a + b)) + 1 := by
  cases c with
  | zero => omega
  | succ c =>
    cases d with
    | zero => omega
    | succ d =>
      simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

private theorem monomial_right (e : ONote) (c : ℕ+) (b : ONote) :
    treeWeight b ≤ treeWeight (rawMonomialProduct e c b) := by
  induction b with
  | zero => simp [rawMonomialProduct, treeWeight]
  | oadd f d u ihf ihu =>
    have hcd : (d : Nat) ≤ (c : Nat) * (d : Nat) := by
      simpa using Nat.mul_le_mul_right (d : Nat) (show 1 ≤ (c : Nat) from c.pos)
    have hpart := Nat.mul_le_mul hcd
      (show 1 + treeWeight f ≤ 1 + (treeWeight e + treeWeight f) by omega)
    simpa only [rawMonomialProduct, rawNaturalSum_norm, treeWeight, PNat.mul_coe,
      Nat.add_zero] using Nat.add_le_add hpart ihu

private theorem monomial_lower (e : ONote) (c : ℕ+) {b : ONote} (hb : b ≠ .zero) :
    (c : Nat) * (1 + treeWeight e) + treeWeight b ≤
      treeWeight (rawMonomialProduct e c b) + 1 := by
  cases b with
  | zero => exact False.elim (hb rfl)
  | oadd f d u =>
    have hp := paired_lower (c : Nat) (d : Nat) (treeWeight e) (treeWeight f) c.pos d.pos
    have hu := monomial_right e c u
    simp only [rawMonomialProduct, rawNaturalSum_norm, treeWeight, PNat.mul_coe,
      Nat.add_zero]
    omega

private theorem product_left (a : ONote) {b : ONote} (hb : b ≠ .zero) :
    treeWeight a ≤ treeWeight (rawNaturalProduct a b) := by
  induction a with
  | zero => simp [rawNaturalProduct, treeWeight]
  | oadd e c t ihe iht =>
    have hm := monomial_lower e c hb
    have hp := weight_positive hb
    have hmon : (c : Nat) * (1 + treeWeight e) ≤ treeWeight (rawMonomialProduct e c b) := by omega
    simpa only [rawNaturalProduct, rawNaturalSum_norm, treeWeight] using Nat.add_le_add hmon iht

private theorem product_lower {a b : ONote} (ha : a ≠ .zero) (hb : b ≠ .zero) :
    treeWeight a + treeWeight b ≤ treeWeight (rawNaturalProduct a b) + 1 := by
  cases a with
  | zero => exact False.elim (ha rfl)
  | oadd e c t =>
    have hm := monomial_lower e c hb
    have ht := product_left t hb
    simp only [rawNaturalProduct, rawNaturalSum_norm, treeWeight]
    omega

private theorem nonzero_note (x : NONote) (hx : 0 < x.1.repr) : x.1 ≠ .zero := by
  intro h
  rw [h] at hx
  exact (lt_irrefl (0 : Ordinal)) hx

theorem actualPositiveOrdinalNorm : Targets.ActualPositiveOrdinalNorm := by
  intro a ha he
  obtain ⟨x, hx⟩ := normalRepresentationComplete a he
  rw [← hx] at ha ⊢
  rw [actualOrdinalNorm_notationCorrespondence x]
  exact weight_positive (nonzero_note x ha)

theorem actualNaturalProductNormLower : Targets.ActualNaturalProductNormLower := by
  intro a b ha hb hae hbe
  obtain ⟨x, hx⟩ := normalRepresentationComplete a hae
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hbe
  rw [← hx] at ha
  rw [← hy] at hb
  have h := product_lower (nonzero_note x ha) (nonzero_note y hb)
  rw [← hx, ← hy, ← naturalProductDenotation x y,
    actualOrdinalNorm_notationCorrespondence x, actualOrdinalNorm_notationCorrespondence y,
    actualOrdinalNorm_notationCorrespondence (naturalProduct x y)]
  change treeWeight x.1 + treeWeight y.1 - 1 ≤ treeWeight (rawNaturalProduct x.1 y.1)
  omega

theorem actualNaturalProductComponentNorm : Targets.ActualNaturalProductComponentNorm := by
  intro a b ha hb hae hbe
  have h := actualNaturalProductNormLower a b ha hb hae hbe
  have hpa := actualPositiveOrdinalNorm a ha hae
  have hpb := actualPositiveOrdinalNorm b hb hbe
  constructor <;> omega

end LogicLineages.OrdinalComparison.Source.OriginalDomain
