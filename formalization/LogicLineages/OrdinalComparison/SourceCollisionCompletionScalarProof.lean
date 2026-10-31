module
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionTargets
public import LogicLineages.OrdinalComparison.WWOriginalAssignmentNormProof
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof
public import LogicLineages.OrdinalComparison.WWOriginalSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open OriginalDomain

theorem raw_of_assignment {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (t : OriginalTerm Γ .ground) (v : OrdinalVector Γ 0) (n : Nat)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v)
    (hn : denote ν (v 0) = (n : Ordinal)) : rawScalar ν t = n := by
  unfold rawScalar
  rw [hv]
  change finiteValue (denote ν (v 0)) = n
  rw [hn]
  exact originalFiniteValueCalibration n

theorem actualScalarTotal : Targets.ActualScalarTotal := by
  intro Γ t
  obtain ⟨v, hv, hg, hb⟩ := originalSourceAssignmentBounded Γ .ground OrdinalSyntax.defaultPolicy t
  refine ⟨v, hv, ?_⟩
  intro ρ
  obtain ⟨n, hn⟩ := originalAmbientScalarFinite Γ (v 0) (hg 0) ρ
  have he : rawScalar (valuation ρ) t = n := raw_of_assignment _ t v n hv hn
  constructor
  · rw [he]
    exact hn
  · have hp := originalScalarPositiveValue Γ (v 0) (hg 0) ρ
    rw [hn, originalFiniteValueCalibration] at hp
    omega

theorem scalar_exact {Γ} (t : OriginalTerm Γ .ground) (v : OrdinalVector Γ 0)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v)
    (ρ : AdmissibleSubstitution Γ) :
    denote (valuation ρ) (v 0) = (rawScalar (valuation ρ) t : Ordinal) ∧
      0 < rawScalar (valuation ρ) t := by
  obtain ⟨w, hw, hs⟩ := actualScalarTotal Γ t
  rw [hv] at hw
  cases Option.some.inj hw
  exact hs ρ
end LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof
