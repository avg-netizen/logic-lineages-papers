module
public import LogicLineages.OrdinalComparison.WWSourceTupleEvaluationTargets
public import LogicLineages.OrdinalComparison.WWEncodedScalarProof
public import LogicLineages.OrdinalComparison.WWScalarTranslationProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open AdmissibleAssignment

theorem actualSourceTupleEvaluation : Targets.ActualSourceTupleEvaluation := by
  refine ⟨encodedScalarComputable, ?_⟩
  intro Γ hΓ τ p t
  obtain ⟨v, hv, hg⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  obtain ⟨s, hs⟩ := generatedGroundScalarTranslationTotal Γ hΓ (v 0) (hg 0)
  refine ⟨v, hv, s, hs, fun xs => ?_⟩
  rw [encodedScalarSourceCorrect]
  exact scalarTranslationSound Γ (v 0) s hs _
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
