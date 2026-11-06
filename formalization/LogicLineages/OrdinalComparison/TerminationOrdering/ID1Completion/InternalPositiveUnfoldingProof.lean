module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution PositiveArithmeticSchemas
open InternalCalculus InternalPositiveUnfoldingSupportProof

theorem actualPositiveContraction : InternalPositiveUnfoldingTargets.ActualPositiveContraction := by
  intro body α p
  exact positiveContraction body p

theorem actualBodyInvariantStep : InternalPositiveUnfoldingTargets.ActualBodyInvariantStep := by
  intro body α
  obtain ⟨d⟩ := positiveContraction body (bodyWithParameters body α)
  unfold replacedBody
  rw [liftBodyInvariant]
  exact ⟨Derivation.implicationElimination (weakenClosed d _) (Derivation.hypothesis (by simp))⟩

theorem actualInternalReverseUnfolding : InternalPositiveUnfoldingTargets.ActualInternalReverseUnfolding := by
  intro body α
  exact InternalCalculusProof.actualInternalInvariantInduction body α []
    (bodyWithParameters body α).formula (actualBodyInvariantStep body α)

theorem actualInternalUnfolding : InternalPositiveUnfoldingTargets.ActualInternalUnfolding := by
  intro body α t
  obtain ⟨backward⟩ := actualInternalReverseUnfolding body α
  have db := Derivation.universalElimination t backward
  have df := Derivation.universalElimination t
    (Derivation.inductiveClosure (body := body) (α := α) (Gamma := []))
  exact ⟨Derivation.conjunctionIntroduction db df⟩

theorem actualOriginalSourceUnfolding : InternalPositiveUnfoldingTargets.ActualOriginalSourceUnfolding := by
  intro data context α t
  exact actualInternalUnfolding (SourcePresentation.sourceBody data context) α t

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingProof
