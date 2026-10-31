module
public import LogicLineages.OrdinalComparison.WWOriginalDescentNormTargets
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof
public import LogicLineages.OrdinalComparison.WWOriginalPowerNormProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem sum_below {a b : Ordinal} (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalSum a b < epsilonZero := by
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hb
  rw [← hx, ← hy, ← naturalSumDenotation x y]
  exact normalRepresentationSound (naturalSum x y)

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

theorem originalAddChildNorm : Targets.OriginalAddChildNorm := by
  intro Γ ρ i f g hf hg
  have h := actualNaturalSumNormAdditivity (expressionValue ρ f) (expressionValue ρ g)
    (originalExpressionValueBelowEpsilonZero Γ ρ f) (originalExpressionValueBelowEpsilonZero Γ ρ g)
  change actualOrdinalNorm (expressionValue ρ f) ≤ actualOrdinalNorm
    (ordinalNaturalSum (expressionValue ρ f) (expressionValue ρ g)) ∧
    actualOrdinalNorm (expressionValue ρ g) ≤ actualOrdinalNorm
    (ordinalNaturalSum (expressionValue ρ f) (expressionValue ρ g))
  rw [h]
  constructor <;> omega

theorem originalExpChildNorm : Targets.OriginalExpChildNorm := by
  intro Γ ρ i f g hi hf hg
  have hfe := originalExpressionValueBelowEpsilonZero Γ ρ f
  have hge := originalExpressionValueBelowEpsilonZero Γ ρ g
  have hgp := originalAmbientGradePositive Γ i g hg ρ
  have hpp : (0 : Ordinal) < (2 : Ordinal) ^ expressionValue ρ f :=
    Ordinal.opow_pos _ (by exact_mod_cast (show (0 : Nat) < 2 by omega))
  have hp := actualNaturalProductComponentNorm _ _ hpp hgp (two_power_below hfe) hge
  have hi' := actualBaseTwoInverseNorm (expressionValue ρ f) hfe
  exact ⟨hi'.trans (Nat.mul_le_mul_left 2 hp.1), hp.2⟩

theorem originalCollapseChildNorm : Targets.OriginalCollapseChildNorm := by
  intro Γ ρ f g hf hg
  let a := expressionValue ρ f
  let b := expressionValue ρ g
  let head := ordinalNaturalProduct Ordinal.omega0 a
  let arg := ordinalNaturalSum head b
  have hae : a < epsilonZero := originalExpressionValueBelowEpsilonZero Γ ρ f
  have hbe : b < epsilonZero := originalExpressionValueBelowEpsilonZero Γ ρ g
  have hap : 0 < a := originalAmbientGradePositive Γ 1 f hf ρ
  have hω : Ordinal.omega0 < epsilonZero := originalClosedValueBelowEpsilonZero .omega
  have hhead : head < epsilonZero := product_below hω hae
  have harg : arg < epsilonZero := sum_below hhead hbe
  have hprod := (actualNaturalProductComponentNorm Ordinal.omega0 a
    Ordinal.omega0_pos hap hω hae).2
  have hsum := actualNaturalSumNormAdditivity head b hhead hbe
  have hcollapse := actualCollapseDominatesNorm arg harg
  have hfinite := (finiteNorm (actualCollapse arg)).2
  change actualOrdinalNorm a ≤ actualOrdinalNorm (actualCollapse arg : Ordinal) ∧
    actualOrdinalNorm b ≤ actualOrdinalNorm (actualCollapse arg : Ordinal)
  rw [hfinite]
  change actualOrdinalNorm a ≤ actualOrdinalNorm head at hprod
  change actualOrdinalNorm arg = actualOrdinalNorm head + actualOrdinalNorm b at hsum
  constructor <;> omega

end LogicLineages.OrdinalComparison.Source.OriginalDomain
