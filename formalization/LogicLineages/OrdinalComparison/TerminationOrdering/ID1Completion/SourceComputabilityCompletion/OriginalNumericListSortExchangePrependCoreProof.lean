module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePrependTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeIntroductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePrependCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalNumericListSortExchange

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] edge sourceEndpoint targetEndpoint front first second tail afterSecond afterFirst firstSecond secondFirst
theorem atValues (source target certificate frontCode payloadCode value newFront newCertificate newSource newTarget : OTerm alpha) (v : Fin 8 → OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edge (suc z) source target certificate)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing certificate frontCode payloadCode)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode newFront value frontCode)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newCertificate newFront payloadCode)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode newSource value source)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode newTarget value target)))
 (hq : ∀ i : Fin 8, Nonempty (Derivation body Delta (programGraph (![first,rest,second,tail,afterSecond,afterFirst,firstSecond,secondFirst] i) (v i)
   (Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0)))))) :
 Nonempty (Derivation body Delta (graph3 edge (suc z) newSource newTarget newCertificate)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0))
 let ys : Fin 3 → OTerm alpha := Fin.cons newSource (Fin.cons newTarget (Fin.cons newCertificate Fin.elim0))
 have certOld : Nonempty (Derivation body Delta (programGraph (.projection 2) certificate xs)) := projectionValue (2 : Fin 3) xs
 have certNew : Nonempty (Derivation body Delta (programGraph (.projection 2) newCertificate ys)) := projectionValue (2 : Fin 3) ys
 have ofront : Nonempty (Derivation body Delta (programGraph front frontCode xs)) := by
   simpa only [front,leftOf] using unaryValue InternalUnpair.left (.projection 2) frontCode certificate xs (pairLeft _ _ _ hp) certOld
 have opayload : Nonempty (Derivation body Delta (programGraph payload payloadCode xs)) := by
   simpa only [payload,rightOf] using unaryValue InternalUnpair.right (.projection 2) payloadCode certificate xs (pairRight _ _ _ hp) certOld
 have nfront : Nonempty (Derivation body Delta (programGraph front newFront ys)) := by
   simpa only [front,leftOf] using unaryValue InternalUnpair.left (.projection 2) newFront newCertificate ys (pairLeft _ _ _ hn) certNew
 have npayload : Nonempty (Derivation body Delta (programGraph payload payloadCode ys)) := by
   simpa only [payload,rightOf] using unaryValue InternalUnpair.right (.projection 2) payloadCode newCertificate ys (pairRight _ _ _ hn) certNew
 have o0 : Nonempty (Derivation body Delta (programGraph first (v 0) xs)) := hq 0
 have o1 : Nonempty (Derivation body Delta (programGraph rest (v 1) xs)) := hq 1
 have o2 : Nonempty (Derivation body Delta (programGraph second (v 2) xs)) := hq 2
 have o3 : Nonempty (Derivation body Delta (programGraph tail (v 3) xs)) := hq 3
 have o4 : Nonempty (Derivation body Delta (programGraph afterSecond (v 4) xs)) := hq 4
 have o5 : Nonempty (Derivation body Delta (programGraph afterFirst (v 5) xs)) := hq 5
 have o6 : Nonempty (Derivation body Delta (programGraph firstSecond (v 6) xs)) := hq 6
 have o7 : Nonempty (Derivation body Delta (programGraph secondFirst (v 7) xs)) := hq 7
 have a0 := unaryRecover InternalUnpair.left payload (v 0) payloadCode xs
   (by simpa only [first,leftOf] using o0) opayload
 have n0 : Nonempty (Derivation body Delta (programGraph first (v 0) ys)) := by
   simpa only [first,leftOf] using unaryValue InternalUnpair.left payload (v 0) payloadCode ys a0 npayload
 have a1 := unaryRecover InternalUnpair.right payload (v 1) payloadCode xs
   (by simpa only [rest,rightOf] using o1) opayload
 have n1 : Nonempty (Derivation body Delta (programGraph rest (v 1) ys)) := by
   simpa only [rest,rightOf] using unaryValue InternalUnpair.right payload (v 1) payloadCode ys a1 npayload
 have a2 := unaryRecover InternalUnpair.left rest (v 2) (v 1) xs
   (by simpa only [second,leftOf] using o2) o1
 have n2 : Nonempty (Derivation body Delta (programGraph second (v 2) ys)) := by
   simpa only [second,leftOf] using unaryValue InternalUnpair.left rest (v 2) (v 1) ys a2 n1
 have a3 := unaryRecover InternalUnpair.right rest (v 3) (v 1) xs
   (by simpa only [tail,rightOf] using o3) o1
 have n3 : Nonempty (Derivation body Delta (programGraph tail (v 3) ys)) := by
   simpa only [tail,rightOf] using unaryValue InternalUnpair.right rest (v 3) (v 1) ys a3 n1
 have a4 := binaryRecover InternalListCodec.consCode second tail (v 4) (v 2) (v 3) xs
   (by simpa only [afterSecond,consOf] using o4) o2 o3
 have n4 : Nonempty (Derivation body Delta (programGraph afterSecond (v 4) ys)) := by
   simpa only [afterSecond,consOf] using binaryValue InternalListCodec.consCode second tail (v 4) (v 2) (v 3) ys a4 n2 n3
 have a5 := binaryRecover InternalListCodec.consCode first tail (v 5) (v 0) (v 3) xs
   (by simpa only [afterFirst,consOf] using o5) o0 o3
 have n5 : Nonempty (Derivation body Delta (programGraph afterFirst (v 5) ys)) := by
   simpa only [afterFirst,consOf] using binaryValue InternalListCodec.consCode first tail (v 5) (v 0) (v 3) ys a5 n0 n3
 have a6 := binaryRecover InternalListCodec.consCode first afterSecond (v 6) (v 0) (v 4) xs
   (by simpa only [firstSecond,consOf] using o6) o0 o4
 have n6 : Nonempty (Derivation body Delta (programGraph firstSecond (v 6) ys)) := by
   simpa only [firstSecond,consOf] using binaryValue InternalListCodec.consCode first afterSecond (v 6) (v 0) (v 4) ys a6 n0 n4
 have a7 := binaryRecover InternalListCodec.consCode second afterFirst (v 7) (v 2) (v 5) xs
   (by simpa only [secondFirst,consOf] using o7) o2 o5
 have n7 : Nonempty (Derivation body Delta (programGraph secondFirst (v 7) ys)) := by
   simpa only [secondFirst,consOf] using binaryValue InternalListCodec.consCode second afterFirst (v 7) (v 2) (v 5) ys a7 n2 n5
 obtain ⟨os,ot⟩ := OriginalNumericListSortExchangeProof.endpointsAt source target certificate he
 have aps := binaryRecover InternalApplicationValidityStackAppend.append front firstSecond source frontCode (v 6) xs
   (by simpa only [sourceEndpoint] using os) ofront o6
 have apt := binaryRecover InternalApplicationValidityStackAppend.append front secondFirst target frontCode (v 7) xs
   (by simpa only [targetEndpoint] using ot) ofront o7
 have nps := InternalApplicationValidityStackAppendListProof.consBackward newFront value frontCode (v 6) source newSource hf aps hs
 have npt := InternalApplicationValidityStackAppendListProof.consBackward newFront value frontCode (v 7) target newTarget hf apt ht
 have es : Nonempty (Derivation body Delta (programGraph sourceEndpoint newSource ys)) := by
   simpa only [sourceEndpoint] using binaryValue InternalApplicationValidityStackAppend.append front firstSecond newSource newFront (v 6) ys nps nfront n6
 have et : Nonempty (Derivation body Delta (programGraph targetEndpoint newTarget ys)) := by
   simpa only [targetEndpoint] using binaryValue InternalApplicationValidityStackAppend.append front secondFirst newTarget newFront (v 7) ys npt nfront n7
 have ms : Nonempty (Derivation body Delta (programGraph sourceMatch (suc z) ys)) := by
   simpa only [sourceMatch,OriginalRawSyntaxTransport.sameOf,InternalApplicationStepPeel.same] using sameAccept (.projection 0) sourceEndpoint newSource ys (projectionValue 0 ys) es
 have mt : Nonempty (Derivation body Delta (programGraph targetMatch (suc z) ys)) := by
   simpa only [targetMatch,OriginalRawSyntaxTransport.sameOf,InternalApplicationStepPeel.same] using sameAccept (.projection 1) targetEndpoint newTarget ys (projectionValue 1 ys) et
 simpa only [edge] using conjunctionAccept sourceMatch targetMatch ys ms mt
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePrependCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePrependCoreProof
