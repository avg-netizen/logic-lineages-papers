module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs [domain,Object]. Extend the ACTUAL original context code by cons,
then weaken only the original packed payload at cutoff zero. No canonical
selector, source checker or calibrated final tuple is changed. -/
def shiftObjectRaw : Program 2 :=
  pairOf (consOf (.projection 0) (leftOf (.projection 1)))
    (.composition shiftPackedRaw ![constant 2 0,rightOf (.projection 1)])

/-- Input [Object]. Read the erased type and remaining context from the
original total list destructors. The non-cons case remains total, but the
context-erasure interpretation is asserted only with an actual cons witness. -/
def eraseObjectRaw : Program 1 :=
  pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => InternalUnpair.left))
    (.composition erasePackedRaw
      ![.composition InternalListCodec.headCode (fun _ : Fin 1 => InternalUnpair.left),
        constant 1 0,InternalUnpair.right])

/-- Counts all original variable occurrences in the raw packed payload. -/
def variableRankObjectRaw : Program 1 :=
  .composition variableRankPackedRaw (fun _ : Fin 1 => InternalUnpair.right)

/-- Every witness is attached to the SAME input/output Object pair. The
context is a symbolic arithmetic code, not an assumed native Lean context. -/
def ShiftRecovered {alpha : Type}
    (d input shifted gamma packed extendedGamma shiftedPacked : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing input gamma packed ⊓
    (graph2 InternalListCodec.consCode extendedGamma d gamma ⊓
      (graph2 shiftPackedRaw shiftedPacked (numeral 0) packed ⊓
        graph2 InternalPairing.pairing shifted extendedGamma shiftedPacked))

/-- Erasure exposes the original packed transformer and exact remaining
context, retaining the supplied context-cons and input-pair witnesses. -/
def EraseRecovered {alpha : Type}
    (d input erased gamma packed extendedGamma erasedPacked : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing input extendedGamma packed ⊓
    (graph2 InternalListCodec.consCode extendedGamma d gamma ⊓
      (graph3 erasePackedRaw erasedPacked d (numeral 0) packed ⊓
        graph2 InternalPairing.pairing erased gamma erasedPacked))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransport
