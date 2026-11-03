module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxInductionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts FiniteObservationBits RecursiveNaturalDomains TypedValueEnvironment
open CoherentConstructorLattice ConfinedStructuralInterpretation RelatedEnvironments ActualValueLogicalRelation
open SourceConstructorIteration ActualComparisonCompleteness TypedObservationAccess RecursiveComparison RelationalSyntax

theorem actualJointFundamental : RelationalSyntaxTargets.ActualJointFundamental :=
  RelationalSyntaxInductionProof.actualJointFundamental

theorem actualIdentityBitSoundness : RelationalSyntaxTargets.ActualIdentityBitSoundness := by
  intro Symbol inst arity I above dec P sigma q o
  have hr : EnvironmentRelated I above P (identity I P) (fun v => MarkedTerm.var v) := by
    intro tau v
    exact LogicalRelationWorldsProof.literalVariableRelated Symbol inst arity I above tau P v
  have H := (actualJointFundamental Symbol inst arity I above dec).1 _ sigma q |>.1 P (identity I P) (fun v => .var v) hr
  rw [SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity _ sigma q.val] at H
  exact RelationalSyntaxSupportProof.currentBits above _ q.val H o

theorem actualIdentityAdequacy : RelationalSyntaxTargets.ActualIdentityAdequacy := by
  intro Symbol inst arity I above dec P sigma q o
  have hs := actualIdentityBitSoundness Symbol inst arity I above dec P sigma q o
  exact ⟨⟨hs.1,ActualComparisonCompletenessProof.weakCompleteness Symbol inst arity I above dec P sigma q o⟩,
    ⟨hs.2,ActualComparisonCompletenessProof.strictCompleteness Symbol inst arity I above dec P sigma q o⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RelationalSyntaxProof
