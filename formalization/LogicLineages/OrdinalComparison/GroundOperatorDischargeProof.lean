module
public import LogicLineages.OrdinalComparison.GroundOperatorDischargeTargets
public import LogicLineages.OrdinalComparison.WWGroundClosingProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundOperatorDischarge.Proof

theorem exactHeadClosure : Targets.ExactHeadClosure := by
  intro Γ e
  have hc : GroundClosing.component (groundMap Γ) = ordinalHeadClosureComponent := by
    funext c
    rcases c with ⟨τ,x,j⟩
    cases x <;> rfl
  unfold GroundClosing.expression ordinalHeadClosure
  rw [hc]

theorem wholeAssignment : Targets.WholeAssignment := by
  intro Γ τ p t
  have h := GroundClosing.Proof.assignmentNaturality (.ground :: Γ) Γ τ (groundMap Γ) p t
  have hv : (GroundClosing.vector (groundMap Γ) :
      OrdinalVector (.ground :: Γ) τ.level → OrdinalVector Γ τ.level) =
      (fun u j => ordinalHeadClosure (u j)) := by
    funext u j
    exact exactHeadClosure Γ (u j)
  rw [hv] at h
  exact h

theorem actualFunctionalDischarge : Targets.ActualFunctionalDischarge := by
  intro Γ r p t
  obtain ⟨u,hu,_⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated (.ground :: Γ) (Ty.curriedGround (r+1)) p t
  refine ⟨u, (fun j => ordinalHeadClosure (u j)),hu,?_,(fun _ => rfl),rfl,rfl⟩
  rw [wholeAssignment, hu]
  rfl

theorem operatorWitnessTransport : Targets.OperatorWitnessTransport := by
  intro Γ p h hh
  obtain ⟨r,t,u,hu,he⟩ := hh
  refine ⟨r,close t,(fun j => ordinalHeadClosure (u j)),?_,?_⟩
  · rw [wholeAssignment, hu]
    rfl
  · exact congrArg ordinalHeadClosure he
end LogicLineages.OrdinalComparison.Source.GroundOperatorDischarge.Proof
