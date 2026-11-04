module
public import LogicLineages.OrdinalComparison.ParametricCanonicalObservationDenotationProof
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricCanonicalObservation.Proof

theorem actualAssignmentTransport : Targets.ActualAssignmentTransport := by
  intro G c hc Γ τ t ν hg hf
  obtain ⟨v,hv,hfree⟩ := SourceRestrictedAssignmentFinite.Proof.actualAssignment Γ τ t hg hf
  refine ⟨v,hv,?_⟩
  intro j
  exact omegaFreeTransport G c hc _ _ _ (fun k => ⟨ν k,rfl⟩) (hfree j)

theorem scalarEquivalence : Targets.ScalarEquivalence := by
  intro G c hc Γ t ν hg hf n
  obtain ⟨v,hv,he⟩ := actualAssignmentTransport G c hc Γ Ty.ground t ν hg hf
  constructor
  · rintro ⟨w,hw,hn⟩
    have h : w=v := Option.some.inj (hw.symm.trans hv)
    subst w
    exact ⟨v,hv,(he 0).symm.trans hn⟩
  · rintro ⟨w,hw,hn⟩
    have h : w=v := Option.some.inj (hw.symm.trans hv)
    subst w
    exact ⟨v,hv,(he 0).trans hn⟩
end LogicLineages.OrdinalComparison.Source.ParametricCanonicalObservation.Proof
