module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryClassRowCoherence.GenericProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryClassRowCoherence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary (Membership)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem classRows : Targets.InternalClassRows := by
  intro n arity body alpha Delta seed parameter typ raw context gamma types out candidate targetOut probe hs hp hg ht hc ha hl hm htarget
  have hi := OriginalPrimaryRerootCoherence.Proof.primaryRerootCoherence n arity body alpha Delta
    seed parameter typ raw context gamma types out candidate targetOut hs hp hg ht hc ha hl hm htarget
  exact GenericProof.rows _ _ seed candidate probe parameter out targetOut hl htarget hi
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryClassRowCoherence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryClassRowCoherence.Proof
