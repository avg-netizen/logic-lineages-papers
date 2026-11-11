module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalTargets
open UniformCertificateCompletion OriginalFinalVariableCanonical
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalFinalVariableFixedness : Prop :=
  ∀ (guard : Program 1) (p : GlobalSourcePackage.Inputs), FixednessLaw guard p

def ActualOriginalFinalVariableCancellation : Prop :=
  ∀ (guard : Program 1) (p : GlobalSourcePackage.Inputs), CancellationLaw guard p

def ActualOriginalFinalVariableRankPreservation : Prop :=
  ∀ (guard : Program 1) (p : GlobalSourcePackage.Inputs), RankLaw guard p

def ActualOriginalFinalVariableCanonicalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (p : GlobalSourcePackage.Inputs) (guard : Program 1), Properties n arity p guard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalTargets
