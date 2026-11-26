module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeIntroductionTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalNumericListSortExchange
attribute [local irreducible] edge sourceEndpoint targetEndpoint front first second tail afterSecond afterFirst firstSecond secondFirst

theorem zeroPrefix (typedQ typedR observedTail observedY observedX source target rest payload certificate : OTerm alpha)
 (hRest : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rest typedR observedTail)))
 (hPayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload typedQ rest)))
 (hCertificate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing certificate z payload)))
 (cY : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode observedY typedR observedTail)))
 (cX : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode observedX typedQ observedTail)))
 (cXY : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode source typedQ observedY)))
 (cYX : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode target typedR observedX))) :
 Nonempty (Derivation body Delta (graph3 edge (suc z) source target certificate)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0))
 have hcert : Nonempty (Derivation body Delta (programGraph (.projection 2) certificate xs)) := projectionValue 2 xs
 have hf : Nonempty (Derivation body Delta (programGraph front z xs)) := by
   simpa only [front,leftOf] using unaryValue InternalUnpair.left (.projection 2) z certificate xs (pairLeft _ _ _ hCertificate) hcert
 have hp : Nonempty (Derivation body Delta (programGraph OriginalNumericListSortExchange.payload payload xs)) := by
   simpa only [OriginalNumericListSortExchange.payload,rightOf] using unaryValue InternalUnpair.right (.projection 2) payload certificate xs (pairRight _ _ _ hCertificate) hcert
 have hq : Nonempty (Derivation body Delta (programGraph first typedQ xs)) := by
   simpa only [first,leftOf] using unaryValue InternalUnpair.left OriginalNumericListSortExchange.payload typedQ payload xs (pairLeft _ _ _ hPayload) hp
 have hr : Nonempty (Derivation body Delta (programGraph OriginalNumericListSortExchange.rest rest xs)) := by
   simpa only [OriginalNumericListSortExchange.rest,rightOf] using unaryValue InternalUnpair.right OriginalNumericListSortExchange.payload rest payload xs (pairRight _ _ _ hPayload) hp
 have hs : Nonempty (Derivation body Delta (programGraph second typedR xs)) := by
   simpa only [second,leftOf] using unaryValue InternalUnpair.left OriginalNumericListSortExchange.rest typedR rest xs (pairLeft _ _ _ hRest) hr
 have ht : Nonempty (Derivation body Delta (programGraph tail observedTail xs)) := by
   simpa only [tail,rightOf] using unaryValue InternalUnpair.right OriginalNumericListSortExchange.rest observedTail rest xs (pairRight _ _ _ hRest) hr
 have hy : Nonempty (Derivation body Delta (programGraph afterSecond observedY xs)) := by
   simpa only [afterSecond,consOf] using binaryValue InternalListCodec.consCode second tail observedY typedR observedTail xs cY hs ht
 have hx : Nonempty (Derivation body Delta (programGraph afterFirst observedX xs)) := by
   simpa only [afterFirst,consOf] using binaryValue InternalListCodec.consCode first tail observedX typedQ observedTail xs cX hq ht
 have hxy : Nonempty (Derivation body Delta (programGraph firstSecond source xs)) := by
   simpa only [firstSecond,consOf] using binaryValue InternalListCodec.consCode first afterSecond source typedQ observedY xs cXY hq hy
 have hyx : Nonempty (Derivation body Delta (programGraph secondFirst target xs)) := by
   simpa only [secondFirst,consOf] using binaryValue InternalListCodec.consCode second afterFirst target typedR observedX xs cYX hs hx
 have heSource : Nonempty (Derivation body Delta (programGraph sourceEndpoint source xs)) := by
   simpa only [sourceEndpoint] using binaryValue InternalApplicationValidityStackAppend.append front firstSecond source z source xs (InternalApplicationValidityStackAppendListProof.appendZeroValue source) hf hxy
 have heTarget : Nonempty (Derivation body Delta (programGraph targetEndpoint target xs)) := by
   simpa only [targetEndpoint] using binaryValue InternalApplicationValidityStackAppend.append front secondFirst target z target xs (InternalApplicationValidityStackAppendListProof.appendZeroValue target) hf hyx
 have hmSource : Nonempty (Derivation body Delta (programGraph sourceMatch (suc z) xs)) := by
   simpa only [sourceMatch,OriginalRawSyntaxTransport.sameOf,InternalApplicationStepPeel.same] using sameAccept (.projection 0) sourceEndpoint source xs (projectionValue 0 xs) heSource
 have hmTarget : Nonempty (Derivation body Delta (programGraph targetMatch (suc z) xs)) := by
   simpa only [targetMatch,OriginalRawSyntaxTransport.sameOf,InternalApplicationStepPeel.same] using sameAccept (.projection 1) targetEndpoint target xs (projectionValue 1 xs) heTarget
 simpa only [edge] using conjunctionAccept sourceMatch targetMatch xs hmSource hmTarget

theorem actualZeroPrefix : OriginalNumericListSortExchangeIntroductionTargets.ZeroPrefix := by
 intro body alpha Delta typedQ typedR observedTail observedY observedX source target rest payload certificate hRest hPayload hCertificate cY cX cXY cYX
 exact zeroPrefix typedQ typedR observedTail observedY observedX source target rest payload certificate hRest hPayload hCertificate cY cX cXY cYX
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeIntroductionProof
