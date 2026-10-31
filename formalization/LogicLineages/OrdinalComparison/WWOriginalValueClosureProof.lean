module
public import LogicLineages.OrdinalComparison.WWOriginalValueClosureTargets
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

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

private theorem omega_below : Ordinal.omega0 < epsilonZero := by
  have h := (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr
    (show (1 : Ordinal) < epsilonZero by simpa using (finiteNorm 1).1)
  simpa only [Ordinal.opow_one, epsilonZero] using h

private theorem two_power_below {a : Ordinal} (ha : a < epsilonZero) :
    (2 : Ordinal) ^ a < epsilonZero := by
  have hω : Ordinal.omega0 ^ a < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ha
  exact (Ordinal.opow_le_opow_left a
    (show (2 : Ordinal) ≤ Ordinal.omega0 from (Ordinal.natCast_lt_omega0 2).le)).trans_lt hω

theorem ordinalExpressionValueBelowEpsilonZero : Targets.OrdinalExpressionValueBelowEpsilonZero := by
  intro ι ρ hρ t
  induction t with
  | var x => exact hρ x
  | zero => exact zero_lt_epsilonZero
  | one => simpa only [denote, Nat.cast_one] using (finiteNorm 1).1
  | omega => exact omega_below
  | add f g ihf ihg => exact sum_below ihf ihg
  | emul f g ihf ihg => exact product_below (two_power_below ihf) ihg
  | collapse f g ihf ihg => exact (finiteNorm _).1

theorem originalClosedValueBelowEpsilonZero : Targets.OriginalClosedValueBelowEpsilonZero := by
  intro t
  exact ordinalExpressionValueBelowEpsilonZero Empty (fun x => nomatch x) (fun x => nomatch x) t

theorem originalAdmissibleValueBelowEpsilonZero : Targets.OriginalAdmissibleValueBelowEpsilonZero := by
  intro Γ ρ x
  rcases x with ⟨τ, v, j⟩
  exact originalClosedValueBelowEpsilonZero (ρ.vector v j)

theorem originalExpressionValueBelowEpsilonZero : Targets.OriginalExpressionValueBelowEpsilonZero := by
  intro Γ ρ t
  exact ordinalExpressionValueBelowEpsilonZero _ (valuation ρ)
    (originalAdmissibleValueBelowEpsilonZero Γ ρ) t

end LogicLineages.OrdinalComparison.Source.OriginalDomain
