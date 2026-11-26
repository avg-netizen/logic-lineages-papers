module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankTargets
open UniformCertificateCompletion OriginalFinalGuardedRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalFinalGuardedTraversalRank : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    TraversalRankLaw p H G W

def ActualOriginalFinalGuardedFoldRank : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    FinalRankLaw p H G W

def ActualOriginalFinalGuardedObjectRank : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    ObjectRankLaw p H G W

def ActualOriginalFinalGuardedRankSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
      Properties n arity p H G W

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankTargets
