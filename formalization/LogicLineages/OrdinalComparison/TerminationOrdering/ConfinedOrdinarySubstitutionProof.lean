module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitutionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitutionProof
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport Source.SourceFreeOccurrences RecursiveComparison
open LiteralContexts ConfinedOrdinarySubstitution

theorem actualSupportPreservation : ConfinedOrdinarySubstitutionTargets.ActualSupportPreservation := by
  intro Symbol arity Gamma Delta tau s t theta hs hf
  rw [SourceFreeOccurrencesProof.exactTypeSupportSubstitution Symbol arity Gamma Delta tau t theta,
    SourceFreeOccurrencesProof.exactTypeSupportSubstitution Symbol arity Gamma Delta tau s theta]
  intro upsilon hm
  rcases Finset.mem_union.mp hm with hOld | hImage
  · exact Finset.mem_union_left _ (hs hOld)
  · obtain ⟨v,hv,htype⟩ := (SourceFreeOccurrencesProof.imageTypeSupportMembership Symbol arity Gamma Delta
      theta (freeOccurrences t) upsilon).mp hImage
    exact Finset.mem_union_right _ ((SourceFreeOccurrencesProof.imageTypeSupportMembership Symbol arity Gamma Delta
      theta (freeOccurrences s) upsilon).mpr ⟨v,hf v hv,htype⟩)

theorem confinedSubstitutionStability : ConfinedOrdinarySubstitutionTargets.ConfinedSubstitutionStability := by
  intro Symbol arity above Gamma Delta tau s t theta
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · have H := OrdinarySubstitutionStabilityProof.weakCovariance Symbol arity above Gamma Delta theta
        ⟨tau,embed s⟩ ⟨tau,embed t⟩ h.1
      rw [SourceMarkedBindingProof.embeddingSubstitution Symbol arity Gamma Delta tau s theta,
        SourceMarkedBindingProof.embeddingSubstitution Symbol arity Gamma Delta tau t theta]
      exact H
    · apply actualSupportPreservation Symbol arity Gamma Delta tau s t theta h.2
      have H := ComparisonFreeVariablesProof.weakFreeVariableContainment Symbol arity above Gamma
        ⟨tau,embed s⟩ ⟨tau,embed t⟩ h.1
      simpa only [ComparisonFreeVariablesProof.ordinaryOccurrenceCalibration Symbol arity Gamma tau s,
        ComparisonFreeVariablesProof.ordinaryOccurrenceCalibration Symbol arity Gamma tau t] using H
  · intro h
    refine ⟨?_,?_⟩
    · have H := OrdinarySubstitutionStabilityProof.strictCovariance Symbol arity above Gamma Delta theta
        ⟨tau,embed s⟩ ⟨tau,embed t⟩ h.1
      rw [SourceMarkedBindingProof.embeddingSubstitution Symbol arity Gamma Delta tau s theta,
        SourceMarkedBindingProof.embeddingSubstitution Symbol arity Gamma Delta tau t theta]
      exact H
    · apply actualSupportPreservation Symbol arity Gamma Delta tau s t theta h.2
      have H := ComparisonFreeVariablesProof.strictFreeVariableContainment Symbol arity above Gamma
        ⟨tau,embed s⟩ ⟨tau,embed t⟩ h.1
      simpa only [ComparisonFreeVariablesProof.ordinaryOccurrenceCalibration Symbol arity Gamma tau s,
        ComparisonFreeVariablesProof.ordinaryOccurrenceCalibration Symbol arity Gamma tau t] using H

def effectiveConfinedDeciders : ConfinedOrdinarySubstitutionTargets.EffectiveConfinedDeciders := by
  intro Symbol inst arity above dec Gamma tau s t
  let I : FiniteObservationBits.Input Symbol arity := ⟨Gamma,tau,tau,s,t⟩
  let answers := OriginalInputDecisionProof.originalComparisonsDecidable Symbol inst arity I above dec
  letI : Decidable (Weak Symbol arity above Gamma ⟨tau,embed s⟩ ⟨tau,embed t⟩) := answers.1
  letI : Decidable (Strict Symbol arity above Gamma ⟨tau,embed s⟩ ⟨tau,embed t⟩) := answers.2
  constructor
  · unfold ConfinedWeak
    infer_instance
  · unfold ConfinedStrict
    infer_instance

theorem confinedWeakReflexivity : ConfinedOrdinarySubstitutionTargets.ConfinedWeakReflexivity := by
  intro Symbol arity above Gamma tau s
  exact ⟨RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above Gamma tau s,Finset.Subset.refl _⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitutionProof
