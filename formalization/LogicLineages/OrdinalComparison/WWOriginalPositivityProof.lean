module
public import LogicLineages.OrdinalComparison.WWOriginalPositivityTargets
public import LogicLineages.OrdinalComparison.WWOriginalNormSumsProof
public import LogicLineages.OrdinalComparison.WWOriginalProductLowerProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem positive_of_norm {a : Ordinal} (h : 0 < actualOrdinalNorm a) : 0 < a := by
  by_contra hn
  have ha : a = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hz : actualOrdinalNorm 0 = 0 := by simpa using (finiteNorm 0).2
  rw [ha, hz] at h
  omega

private theorem sum_positive {a b : Ordinal} (ha : 0 < a)
    (hae : a < epsilonZero) (hbe : b < epsilonZero) : 0 < ordinalNaturalSum a b := by
  apply positive_of_norm
  rw [actualNaturalSumNormAdditivity a b hae hbe]
  have := actualPositiveOrdinalNorm a ha hae
  omega

private theorem product_positive {a b : Ordinal} (ha : 0 < a) (hb : 0 < b)
    (hae : a < epsilonZero) (hbe : b < epsilonZero) : 0 < ordinalNaturalProduct a b := by
  apply positive_of_norm
  have h := actualNaturalProductNormLower a b ha hb hae hbe
  have hna := actualPositiveOrdinalNorm a ha hae
  have hnb := actualPositiveOrdinalNorm b hb hbe
  omega

private theorem product_below {a b : Ordinal} (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalProduct a b < epsilonZero := by
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hb
  rw [← hx, ← hy, ← naturalProductDenotation x y]
  exact normalRepresentationSound (naturalProduct x y)

private theorem two_power_below {a : Ordinal} (ha : a < epsilonZero) :
    (2 : Ordinal) ^ a < epsilonZero := by
  have hω : Ordinal.omega0 ^ a < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ha
  exact (Ordinal.opow_le_opow_left a
    (show (2 : Ordinal) ≤ Ordinal.omega0 from (Ordinal.natCast_lt_omega0 2).le)).trans_lt hω

private theorem collapse_positive {a b : Ordinal} (ha : a < epsilonZero)
    (hb : 0 < b) (hfin : ∃ n : Nat, b = (n : Ordinal)) :
    0 < (actualCollapse (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 a) b) : Ordinal) := by
  obtain ⟨n, rfl⟩ := hfin
  have hn : 0 < n := by exact_mod_cast hb
  have hω : Ordinal.omega0 < epsilonZero := originalClosedValueBelowEpsilonZero .omega
  rw [actualNaturalSumFiniteRight]
  have hc := actualCollapseFiniteTailBound _ (product_below hω ha) n
  exact_mod_cast lt_of_lt_of_le hn hc

theorem originalClosedGradePositive : Targets.OriginalClosedGradePositive := by
  intro i t ht
  induction ht with
  | one i => exact zero_lt_one
  | omega i hi => exact Ordinal.omega0_pos
  | add hf hg ihf ihg =>
    exact sum_positive ihf (originalClosedValueBelowEpsilonZero _) (originalClosedValueBelowEpsilonZero _)
  | emul hi hf hg ihf ihg =>
    exact product_positive (Ordinal.opow_pos _ (by exact_mod_cast (show (0 : Nat) < 2 by omega))) ihg
      (two_power_below (originalClosedValueBelowEpsilonZero _)) (originalClosedValueBelowEpsilonZero _)
  | collapse hf hg hn ihf ihg =>
    exact collapse_positive (originalClosedValueBelowEpsilonZero _) ihg (originalClosedScalarFinite _ hg)
  | promote hi hh ih => exact ih

theorem originalAmbientGradePositive : Targets.OriginalAmbientGradePositive := by
  intro Γ i t ht ρ
  induction ht with
  | one i => exact zero_lt_one
  | omega i hi => exact Ordinal.omega0_pos
  | var x j => exact originalClosedGradePositive j.val _ (ρ.graded x j)
  | add hf hg ihf ihg =>
    exact sum_positive ihf (originalExpressionValueBelowEpsilonZero Γ ρ _)
      (originalExpressionValueBelowEpsilonZero Γ ρ _)
  | emul hi hf hg ihf ihg =>
    exact product_positive (Ordinal.opow_pos _ (by exact_mod_cast (show (0 : Nat) < 2 by omega))) ihg
      (two_power_below (originalExpressionValueBelowEpsilonZero Γ ρ _))
      (originalExpressionValueBelowEpsilonZero Γ ρ _)
  | collapse hf hg hn ihf ihg =>
    exact collapse_positive (originalExpressionValueBelowEpsilonZero Γ ρ _) ihg
      (originalAmbientScalarFinite Γ _ hg ρ)
  | promote hi hh ih => exact ih

theorem originalScalarPositiveValue : Targets.OriginalScalarPositiveValue := by
  intro Γ t ht ρ
  have hp := originalAmbientGradePositive Γ 0 t ht ρ
  obtain ⟨n, hn⟩ := originalAmbientScalarFinite Γ t ht ρ
  rw [hn] at hp ⊢
  rw [originalFiniteValueCalibration]
  have : 0 < n := by exact_mod_cast hp
  omega

end LogicLineages.OrdinalComparison.Source.OriginalDomain
