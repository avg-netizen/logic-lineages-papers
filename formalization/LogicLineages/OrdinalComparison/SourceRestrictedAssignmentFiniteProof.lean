module
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteAssignmentProof
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteDenotationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite.Proof

theorem finiteScalar : Targets.FiniteScalar := by
  intro G Γ t ν hg ht
  obtain ⟨v,hv,hfree⟩ := actualAssignment Γ .ground t hg ht
  obtain ⟨n,hn⟩ := finiteDenotation (OrdinalComponent Γ) G
    (fun c => (ν c : Ordinal)) (v 0) (fun c => ⟨ν c,rfl⟩) (hfree 0)
  exact ⟨n,v,hv,hn⟩
end LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite.Proof
