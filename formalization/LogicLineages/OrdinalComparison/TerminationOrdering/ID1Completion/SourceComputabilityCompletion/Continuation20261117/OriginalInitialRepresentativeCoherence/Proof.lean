module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInitialRepresentativeCoherence.LiteralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInitialRepresentativeCoherence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
attribute [local irreducible] programGraph
/-- Apply guarded coherence at this exact initial tuple's actual source/window. -/
theorem initialCoherence : Targets.InternalInitialCoherence := by
  intro n arity p W body alpha Delta seed parameter typ raw context gamma types out candidate targetOut guardedOut targetGuardedOut hs hp hg ht hc ha hl hm htarget hguarded htargetguarded
  rw [LiteralProof.representative n arity p W] at hguarded htargetguarded
  exact OriginalPrimaryRankGuardCoherence.Proof.rankGuardCoherence n arity _ p.window
    body alpha Delta seed parameter typ raw context gamma types out candidate targetOut guardedOut targetGuardedOut
    hs hp hg ht hc ha hl hm htarget hguarded htargetguarded
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInitialRepresentativeCoherence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInitialRepresentativeCoherence.Proof
