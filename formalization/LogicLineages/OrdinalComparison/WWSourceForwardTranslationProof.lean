module
public import LogicLineages.OrdinalComparison.WWSourceForwardTranslationTargets
public import LogicLineages.OrdinalComparison.WWFixedShiftProof
public import LogicLineages.OrdinalComparison.WWScalarTranslationProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open AdmissibleAssignment

private theorem scalar_positive {ι : Type} (s : Scalar ι) (ρ : ι → Nat)
    (hp : ∀ x, 0 < ρ x) : 0 < s.value ρ := by
  induction s with
  | one => exact Nat.zero_lt_one
  | var x => exact hp x
  | add a b iha ihb => exact Nat.add_pos_left iha _
  | shift c a ih =>
    have hb := actualCollapseFiniteTailBound (fixedHead c) (scalarFixedHeadAdmissible c).2 (a.value ρ)
    exact ih.trans_le hb

theorem actualSourceForwardTranslation : Targets.ActualSourceForwardTranslation := by
  refine ⟨scalarFixedHeadAdmissible, scalarFixedShiftComputable, ?_⟩
  intro Γ hΓ τ p t
  obtain ⟨v, hv, gv⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  refine ⟨v, hv, ?_, ?_⟩
  · intro j hj
    have hc := actualGeneratedGroundPositiveClosed Γ hΓ j.val (v j) hj (gv j)
    obtain ⟨c, he⟩ := generatedClosedPositiveEvaluationTotal Γ j.val (v j) (gv j) hj hc
    exact ⟨hc, c, he, closedPositiveValuePositive c, closedPositiveEvaluationSound Γ (v j) c he⟩
  · obtain ⟨s, hs⟩ := generatedGroundScalarTranslationTotal Γ hΓ (v 0) (gv 0)
    exact ⟨s, hs, scalarTranslationSound Γ (v 0) s hs, fun ρ hp => scalar_positive s ρ hp⟩

end LogicLineages.OrdinalComparison.Source.ForwardTranslation
