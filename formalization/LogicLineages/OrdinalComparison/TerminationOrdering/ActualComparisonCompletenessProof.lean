module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessInductionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourcePortContexts FiniteObservationBits TypedValueEnvironment ConfinedStructuralInterpretation RecursiveComparison ActualComparisonCompleteness RenamingEquivariance ActualComparisonCompletenessSupportProof ActualComparisonCompletenessInductionProof

theorem weakCompleteness : ActualComparisonCompletenessTargets.WeakCompleteness := by
  intro Symbol inst arity I above dec P τ q o h
  have he : renamePacked (fun v => v) ⟨τ,observedTerm o⟩=decode o.val o.property.2.1 := by
    have hi := Source.SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity (portTypes P.val++I.context) τ (observedTerm o)
    exact (congrArg (fun t => (⟨τ,t⟩ : RecursiveComparison.Packed Symbol arity _)) hi).trans (targetTyped o).symm
  exact weakMeaning above h P (fun v => v) q.property o.val o.property.1 o.property.2.1 he

theorem strictCompleteness : ActualComparisonCompletenessTargets.StrictCompleteness := by
  intro Symbol inst arity I above dec P τ q o h
  have he : renamePacked (fun v => v) ⟨τ,observedTerm o⟩=decode o.val o.property.2.1 := by
    have hi := Source.SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity (portTypes P.val++I.context) τ (observedTerm o)
    exact (congrArg (fun t => (⟨τ,t⟩ : RecursiveComparison.Packed Symbol arity _)) hi).trans (targetTyped o).symm
  exact strictMeaning above h P (fun v => v) q.property o.val o.property.1 o.property.2.1 he

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessProof
