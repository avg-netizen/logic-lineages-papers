module
public import LogicLineages.StandardControlCurrent.DefaultSourceDomainProof
public import LogicLineages.OrdinalComparison.GroundSourceEqualityProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentPrimitiveProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.DefaultSourceProof
open OrdinalComparison Source Source.OriginalDomain Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem assignment : DefaultSourceTargets.Assignment := by
  refine ⟨DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive,
    DefaultSourceAssignment.Proof.assignmentCorrect, ?_⟩
  intro Γ hΓ τ t
  obtain ⟨v,hv,_⟩ := actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy t
  exact ⟨v,hv⟩

private theorem vector_calibration {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (s : AdmissibleSubstitution Γ) (ρ : OrdinalComponent Γ → Nat)
    (hρ : ∀ c, valuation s c=(ρ c : Ordinal)) (j : Nat) :
    DefaultSourceTargets.vectorAt v s j = sourceVectorAtValue v ρ j := by
  have he : valuation s = fun c => (ρ c : Ordinal) := funext hρ
  simp only [DefaultSourceTargets.vectorAt,sourceVectorAtValue,ordinalVectorAt]
  split <;> simp only [expressionValue,he,denote]

theorem equality : DefaultSourceTargets.Equality := by
  refine ⟨GroundSourceEquality.source_code_computable, ?_⟩
  intro Γ hΓ τ υ a b
  rw [GroundSourceEquality.full_equality.2 Γ hΓ τ υ a b]
  constructor
  · rintro ⟨av,bv,ha,hb,he⟩
    refine ⟨av,bv,ha,hb,?_⟩
    intro s j
    obtain ⟨ρ,hp,hv⟩ := DefaultSourceDomainProof.domain.2 Γ hΓ s
    rw [vector_calibration av s ρ hv j,vector_calibration bv s ρ hv j]
    exact he ρ hp j
  · rintro ⟨av,bv,ha,hb,he⟩
    refine ⟨av,bv,ha,hb,?_⟩
    intro ρ hp j
    obtain ⟨s,hv⟩ := DefaultSourceDomainProof.domain.1 Γ hΓ ρ hp
    rw [←vector_calibration av s ρ hv j,←vector_calibration bv s ρ hv j]
    exact he s j

theorem full : DefaultSourceTargets.FullDefaultSource :=
  ⟨DefaultSourceDomainProof.domain,assignment,equality⟩
end LogicLineages.StandardControlCurrent.DefaultSourceProof
