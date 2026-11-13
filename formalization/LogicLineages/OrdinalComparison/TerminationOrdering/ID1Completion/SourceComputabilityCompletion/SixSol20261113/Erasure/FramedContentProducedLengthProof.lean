module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProducedLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Runtime prefix uniqueness transfers the independently proved exact length
to the fixed content-bearing row, without comparing either execution count. -/
theorem fromPrefix (R : Program 2) (size tagged produced count : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.Completion R size tagged)))
 (hp : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged count produced))) :
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size produced)) := by
 apply VisitListCompletionSyntax.completionCases R size tagged _ hc
 intro beta j Theta oldCount oldRow hinc hrow
 have hp' := renameInto hp j Theta hinc
 rw [PrefixFrameSyntax.frameRename] at hp'
 have he := PrefixValueProof.actualProducedAgreement R body beta Theta
   (tagged.relabel j) oldCount (count.relabel j) oldRow (produced.relabel j) (andRight hrow) hp'
 rw [OriginalContextInsertionSyntaxProof.lengthRename]
 exact headTransport OriginalContextInsertion.length (size.relabel j) oldRow (produced.relabel j)
   Fin.elim0 he (andLeft hrow)
theorem actualLength (R : Program 2) (size tagged produced : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.Completion R size tagged)))
 (hp : Nonempty (Derivation body Delta (ContentVisitsDefinitions.Counted R tagged produced))) :
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size produced)) := by
 apply ContentVisitsSyntax.countedCases R tagged produced _ hp
 intro beta j Theta count hinc hprefix
 have hc' := renameInto hc j Theta hinc
 rw [VisitListCompletionSyntax.completionRename] at hc'
 rw [OriginalContextInsertionSyntaxProof.lengthRename]
 exact fromPrefix R (size.relabel j) (tagged.relabel j) (produced.relabel j) count hc' hprefix
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProducedLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProducedLengthProof
