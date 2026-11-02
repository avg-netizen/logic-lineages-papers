module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesRelationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesProof
open Source Source.SourceMarkedSyntax Source.SourceFreeOccurrences RecursiveComparison ComparisonFreeVariables

theorem ordinaryOccurrenceCalibration : ComparisonFreeVariablesTargets.OrdinaryOccurrenceCalibration := ComparisonFreeVariablesSyntaxProof.ordinaryOccurrenceCalibration
theorem supportCalibration : ComparisonFreeVariablesTargets.SupportCalibration := ComparisonFreeVariablesSyntaxProof.supportCalibration
theorem originalApplyProvenance : ComparisonFreeVariablesTargets.OriginalApplyProvenance := ComparisonFreeVariablesApplicationProof.originalApplyProvenance

theorem weakFreeVariableContainment : ComparisonFreeVariablesTargets.WeakFreeVariableContainment := by
  intro Symbol arity above Γ s t h
  let a : Allowed Γ := fun {σ} v => (⟨σ,v⟩ : PackedVariable Γ) ∈ markedOccurrences s.2
  have hs : Supported s.2 a := (supportCalibration Symbol arity Γ s.1 s.2 a).mpr (by intro v hv; exact hv)
  have ht := ComparisonFreeVariablesRelationProof.weakSupported h a hs
  exact (supportCalibration Symbol arity Γ t.1 t.2 a).mp ht

theorem strictFreeVariableContainment : ComparisonFreeVariablesTargets.StrictFreeVariableContainment := by
  intro Symbol arity above Γ s t h
  let a : Allowed Γ := fun {σ} v => (⟨σ,v⟩ : PackedVariable Γ) ∈ markedOccurrences s.2
  have hs : Supported s.2 a := (supportCalibration Symbol arity Γ s.1 s.2 a).mpr (by intro v hv; exact hv)
  have ht := ComparisonFreeVariablesRelationProof.strictSupported h a hs
  exact (supportCalibration Symbol arity Γ t.1 t.2 a).mp ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesProof
