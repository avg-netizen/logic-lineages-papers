module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankObjectProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankSelectionProof
open UniformCertificateCompletion OriginalFinalGuardedRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Retain every previous property at the very same selected tuple. This
conditional helper does not assert that its traversal supplier is proved. -/
theorem selection
    (law : OriginalFinalGuardedRankTargets.ActualOriginalFinalGuardedTraversalRank) :
    OriginalFinalGuardedRankTargets.ActualOriginalFinalGuardedRankSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    OriginalRankGuardedRepresentativeGlobalProof.actualOriginalRankGuardedRepresentativeSelection n arity
  have ht := law p H G W
  have hf := OriginalFinalGuardedRankFoldProof.foldRank p H G W ht
  exact ⟨p,H,G,W,hprevious,ht,hf,OriginalFinalGuardedRankObjectProof.objectRank p H G W hf⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankSelectionProof
