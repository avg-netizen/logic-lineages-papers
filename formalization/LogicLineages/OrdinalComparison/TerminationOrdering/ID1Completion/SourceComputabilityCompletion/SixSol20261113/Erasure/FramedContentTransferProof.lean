module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueAgreementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FramedContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- A content-bearing canonical subtree run determines every actual framed
result, without relating their counts. This does not itself supply that run. -/
theorem fromCanonical (R : Program 2) (job count value canonicalCount canonicalValue : OTerm alpha)
 (ha : Nonempty (Derivation body Delta
   (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job canonicalCount canonicalValue)))
 (hc : Nonempty (Derivation body Delta (Content R job canonicalValue)))
 (hf : Nonempty (Derivation body Delta
   (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value))) :
 Nonempty (Derivation body Delta (Content R job value)) := by
 have he := Runtime.FramedValueAgreementProof.actualFramedValueAgreement R body alpha Delta
   job canonicalCount count canonicalValue value ha hf
 exact outputTransport (contentProgram R) canonicalValue value (Fin.cons job Fin.elim0) he hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentTransferProof
