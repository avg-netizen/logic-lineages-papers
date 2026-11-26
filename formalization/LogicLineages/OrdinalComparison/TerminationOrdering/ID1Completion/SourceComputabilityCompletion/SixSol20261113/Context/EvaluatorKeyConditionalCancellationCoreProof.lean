module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyConditionalCancellationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalOutputDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyShiftDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyConditionalCancellationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRawSyntaxTransport (constant)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atCoordinates (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input raw gamma context parameter d shifted canonicalShift erased erasedRaw out originalOut
 extended shiftedRaw extendedParameter canonicalRaw erasedQuery : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input gamma raw)))
 (hpp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hd : Nonempty (Derivation body Delta (Domain p H G W raw parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 OriginalRawObjectTransport.shiftObjectRaw shifted d input)))
 (hk : Nonempty (Derivation body Delta (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) canonicalShift context shifted)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalRawObjectTransport.eraseObjectRaw erased canonicalShift)))
 (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right erasedRaw erased)))
 (hSame : Nonempty (Derivation body Delta (Same p H G W erasedRaw raw parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) out context erased)))
 (hor : Nonempty (Derivation body Delta (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) originalOut context input)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.shiftPackedRaw shiftedRaw (numeral 0) raw)))
 (hep : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing extendedParameter context extended)))
 (hcr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right canonicalRaw canonicalShift)))
 (heq : Nonempty (Derivation body Delta (graph1 OriginalRawObjectTransportInternalSupportProof.erasedPayload erasedQuery canonicalShift)))
 : Nonempty (Derivation body Delta (equal out originalOut)) := by
 let xs : Fin 2 → OTerm alpha := ![d,input]
 have hleft := unaryValue InternalUnpair.left (.projection 1) gamma input xs
   (pairLeft input gamma raw hp) (projectionValue 1 xs)
 have hright := unaryValue InternalUnpair.right (.projection 1) raw input xs
   (pairRight input gamma raw hp) (projectionValue 1 xs)
 have hext := binaryValue InternalListCodec.consCode (.projection 0)
   OriginalRawObjectTransportInternalSupportProof.sourceContext extended d gamma xs hc (projectionValue 0 xs) hleft
 have hshift := binaryValue OriginalRawSyntaxTransport.shiftPackedRaw (constant 2 0)
   OriginalRawObjectTransportInternalSupportProof.sourcePacked shiftedRaw (numeral 0) raw xs ht (constantValue 0 xs) hright
 have hsp := binaryRecover InternalPairing.pairing
   OriginalRawObjectTransportInternalSupportProof.extendedContext
   OriginalRawObjectTransportInternalSupportProof.shiftedPayload shifted extended shiftedRaw xs hs hext hshift
 have hi := OriginalContextInsertionZeroProof.zeroBackward d gamma extended hc
 have hsd := EvaluatorKeyShiftDomainProof.actualShiftDomain p H G W body alpha Delta
   raw shiftedRaw d (numeral 0) gamma extended context parameter extendedParameter hd hi hpp hep ht
 have hcd := EvaluatorKeyFinalOutputDomainProof.actualObjectDomain p H G W P body alpha Delta
   context shifted canonicalShift extended shiftedRaw canonicalRaw extendedParameter hsp hep hsd hk hcr
 have hrec := OriginalRawObjectTransportInternalSupportProof.eraseRecoveredAt
   d canonicalShift erased gamma canonicalRaw extended erasedQuery (andRight hcd) hc he heq
 have hpair := andRight (andRight (andRight hrec))
 have hval := valueUnique InternalUnpair.right erasedQuery erasedRaw (![erased])
   (pairRight erased gamma erasedQuery hpair) hr
 have herase := outputTransport OriginalRawSyntaxTransport.erasePackedRaw erasedQuery erasedRaw
   (![d,numeral 0,canonicalRaw]) hval (andLeft (andRight (andRight hrec)))
 have hed := EvaluatorKeyDomainClosureProof.actualErasureDomain p H G W body alpha Delta
   canonicalRaw erasedRaw d (numeral 0) gamma extended context extendedParameter parameter
   (andLeft hcd) hi hep hpp herase
 have hep' := reconstructPair erased gamma erasedRaw (pairLeft erased gamma erasedQuery hpair) hr
 exact EvaluatorKeyObjectProof.actualObjectEquality p H G W P body alpha Delta
   erased input erasedRaw raw out originalOut context gamma parameter hep' hp hpp hed hd hSame ho hor
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyConditionalCancellationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyConditionalCancellationCoreProof
