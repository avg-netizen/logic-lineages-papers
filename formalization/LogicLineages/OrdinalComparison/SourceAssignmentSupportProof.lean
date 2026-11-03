module
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportAssignmentProof
public import LogicLineages.OrdinalComparison.TrackedSourceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AssignmentSupport.Proof
open SourceFreeOccurrences AdmissibleAssignment

theorem actualTrackedInactive : Targets.ActualTrackedInactive := by
  intro k Γ F n e
  obtain ⟨v,hv,hs,hscalar⟩ := fullActualAssignmentSupport Γ (Ty.curriedGround n) OrdinalSyntax.defaultPolicy (TrackedSource.erase e)
  refine ⟨v,hv,?_⟩
  have ha := TrackedSource.Proof.exactActivity k Γ F n e
  constructor
  · intro hinactive j hmem
    have hsource := hs j _ hmem
    have hactive := ha.mpr hsource
    rw [hinactive] at hactive
    cases hactive
  · intro hfree
    cases he : TrackedSource.active e with
    | false => rfl
    | true =>
      have hsource := ha.mp he
      exact False.elim (hfree 0 ((hscalar _).mpr hsource))
end LogicLineages.OrdinalComparison.Source.AssignmentSupport.Proof
