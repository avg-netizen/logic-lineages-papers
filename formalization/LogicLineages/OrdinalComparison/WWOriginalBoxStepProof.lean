module
public import LogicLineages.OrdinalComparison.WWOriginalBoxStepTargets
public import LogicLineages.OrdinalComparison.WWOriginalPowerNormProof
public import LogicLineages.OrdinalComparison.WWOriginalNormSumsProof
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain

theorem actualNaturalProductUpperNorm : Targets.ActualNaturalProductUpperNorm := by
  intro a b ha hb
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hb
  rw [← hx, ← hy, ← naturalProductDenotation x y,
    actualOrdinalNorm_notationCorrespondence (naturalProduct x y),
    actualOrdinalNorm_notationCorrespondence x, actualOrdinalNorm_notationCorrespondence y]
  exact naturalProductNormBound x y

private theorem two_power_below {a : Ordinal} (ha : a < epsilonZero) :
    (2 : Ordinal) ^ a < epsilonZero := by
  have hω : Ordinal.omega0 ^ a < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ha
  exact (Ordinal.opow_le_opow_left a
    (show (2 : Ordinal) ≤ Ordinal.omega0 from (Ordinal.natCast_lt_omega0 2).le)).trans_lt hω

theorem originalBoxStepNorm : Targets.OriginalBoxStepNorm := by
  intro Γ ρ h f g
  have hh := originalExpressionValueBelowEpsilonZero Γ ρ h
  have hp := actualNaturalProductUpperNorm _ _ (two_power_below hh)
    (originalExpressionValueBelowEpsilonZero Γ ρ (.add f g))
  have hs := actualNaturalSumNormAdditivity _ _
    (originalExpressionValueBelowEpsilonZero Γ ρ f)
    (originalExpressionValueBelowEpsilonZero Γ ρ g)
  exact hp.trans (by
    change actualOrdinalNorm ((2 : Ordinal) ^ expressionValue ρ h) *
      actualOrdinalNorm (ordinalNaturalSum (expressionValue ρ f) (expressionValue ρ g)) ≤ _
    rw [hs]
    exact Nat.mul_le_mul_right _ (actualBaseTwoForwardNorm _ hh))

end LogicLineages.OrdinalComparison.Source.OriginalDomain
