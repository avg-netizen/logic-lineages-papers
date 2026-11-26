module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfaceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalCancellation
open OriginalRawSyntaxTransportInternalCancellationBindingProof
open OriginalRawSyntaxTransportInternalInterfaceSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem cancellationAt (raw shifted erased d k : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw (fold .shift) (fold .erase) raw)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftRaw shifted k raw)))
    (he : Nonempty (Derivation body Delta (graph3 eraseRaw erased d k shifted))) :
    Nonempty (Derivation body Delta (equal erased raw)) := by
  have hi := atRawApply (fold .shift) (fold .erase) raw d k shifted h
    (zeroFirstForward (fold .shift) shifted k raw hs)
  simpa only [equalEqn] using valueUnique (fold .erase) erased raw
    (Fin.cons d (Fin.cons k (Fin.cons shifted Fin.elim0))) he hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationAtProof
