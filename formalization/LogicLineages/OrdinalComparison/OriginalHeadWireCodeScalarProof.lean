module
public import LogicLineages.OrdinalComparison.OriginalHeadWireCodeTargets
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
public import LogicLineages.OrdinalComparison.WWOriginalDomainProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode.Proof
open OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem generated_finite {Γ : List Ty} {i : Nat} {q : OrdinalExpression Γ}
    (hg : GeneratedOrdinalGrade Γ i q) (ρ : AdmissibleSubstitution Γ) :
    i=0 → ∃ n : Nat, expressionValue ρ q = (n : Ordinal) := by
  induction hg with
  | one i => intro _; exact ⟨1,by simp [expressionValue,denote]⟩
  | omega i hi => intro he; omega
  | var x j =>
    intro he
    have hj : j=0 := Fin.ext he
    subst j
    exact originalClosedScalarFinite _ (ρ.graded x 0)
  | add hf hg ihf ihg =>
    intro he
    obtain ⟨n,hn⟩ := ihf he
    obtain ⟨m,hm⟩ := ihg he
    refine ⟨n+m,?_⟩
    change ordinalNaturalSum (expressionValue ρ _) (expressionValue ρ _) = _
    rw [hn,hm,naturalSum_finite]
  | emul hi hf hg ihf ihg => intro he; omega
  | collapse hf hg ihf ihg => intro _; exact ⟨_,rfl⟩

theorem actualScalarFiniteness : Targets.ActualScalarFiniteness := by
  intro Γ τ t
  obtain ⟨u,hu,hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy t
  refine ⟨u,hu,?_⟩
  intro ρ
  obtain ⟨n,hn⟩ := generated_finite (hg 0) (UnitObservation.substitution ρ) rfl
  unfold scalarValue
  rw [hn,originalFiniteValueCalibration]
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode.Proof
