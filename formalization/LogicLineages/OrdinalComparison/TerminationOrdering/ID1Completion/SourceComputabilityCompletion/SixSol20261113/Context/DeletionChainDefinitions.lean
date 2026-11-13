module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
/-- One literal operational deletion, with no admission or observation-content
assertion in the transition. Both terms use the same selected type, current
cutoff/context, next context and unchanged outer window. -/
def Transition {alpha : Type}
 (left right nextLeft nextRight parameter nextParameter c gamma nextGamma count cutoff selectedType : OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing parameter c gamma ⊓
 (graph2 InternalPairing.pairing nextParameter c nextGamma ⊓
 (OriginalContextInsertion.lengthGraph count gamma ⊓
 (OriginalContextInsertion.Below cutoff count ⊓
 (graph2 InternalRawListRecursion.lookup selectedType cutoff gamma ⊓
 (graph2 OriginalClassContextAllPositionObserver.deleteAt nextGamma cutoff gamma ⊓
 (graph3 OriginalRawSyntaxTransport.erasePackedRaw nextLeft selectedType cutoff left ⊓
  graph3 OriginalRawSyntaxTransport.erasePackedRaw nextRight selectedType cutoff right))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainDefinitions
