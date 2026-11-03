module
public import LogicLineages.OrdinalComparison.ScalarPartialActivityPartialProof
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportProof
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarPartialActivity.Proof
open SourceFreeOccurrences AdmissibleAssignment AssignmentSupport

theorem fullGroundSourceTransport : Targets.FullGroundSourceTransport := by
  intro Γ τ p t
  obtain ⟨h,hh,hg⟩ := actualAdmissibleAssignmentGenerated (.ground :: Γ) τ p t
  obtain ⟨v,hv,vg⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ .ground p 0 (h 0) (hg 0)
  have hs := AssignmentSupport.Proof.assignment_support p t h hh
  refine ⟨h,v,hh,hv,vg,?_⟩
  intro σ x
  calc
    (⟨σ,x⟩ : PackedVariable Γ)∈names (v 0) ↔
        (⟨σ,x⟩ : PackedVariable Γ)∈(names (h 0)).filterMap dropBound :=
      exactScalarOldNames Γ .ground p (h 0) v hv _
    _ ↔ (⟨σ,Variable.there x⟩ : PackedVariable (.ground :: Γ))∈names (h 0) :=
      TrackedSource.Proof.mem_dropBound x (names (h 0))
    _ ↔ (⟨σ,Variable.there x⟩ : PackedVariable (.ground :: Γ))∈freeOccurrences t := hs.2 _

theorem actualTrackedActivity : Targets.ActualTrackedActivity := by
  intro k Γ F n e
  obtain ⟨h,v,hh,hv,hg,hname⟩ := fullGroundSourceTransport Γ (Ty.curriedGround n)
    OrdinalSyntax.defaultPolicy (TrackedSource.erase e)
  refine ⟨h,v,hh,hv,?_⟩
  exact (TrackedSource.Proof.exactActivity k (.ground :: Γ) (.there F) n e).trans
    (hname (Ty.curriedGround (k+1)) F).symm
end LogicLineages.OrdinalComparison.Source.ScalarPartialActivity.Proof
