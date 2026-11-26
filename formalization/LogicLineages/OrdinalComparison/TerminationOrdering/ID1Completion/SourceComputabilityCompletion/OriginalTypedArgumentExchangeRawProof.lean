module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixAdjacentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeRawProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionClosureLogicProof
open InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentExchange
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] edge sourceEndpoint targetEndpoint sourceSuffix targetSuffix

theorem endpointsAt (source target certificate : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edge (suc z) source target certificate))) :
 Nonempty (Derivation body Delta (graph3 sourceEndpoint source source target certificate)) ∧
 Nonempty (Derivation body Delta (graph3 targetEndpoint target source target certificate)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0))
 have h := conjunctionRecover sourceMatch targetMatch xs (by simpa only [edge] using he)
 constructor
 · exact OriginalConstructorLeafInternalProof.sameKnownLeftRecover (.projection 0) sourceEndpoint source xs
     (by simpa only [sourceMatch,OriginalRawSyntaxTransport.sameOf,InternalApplicationStepPeel.same] using andLeft h) (projectionValue 0 xs)
 · exact OriginalConstructorLeafInternalProof.sameKnownLeftRecover (.projection 1) targetEndpoint target xs
     (by simpa only [targetMatch,OriginalRawSyntaxTransport.sameOf,InternalApplicationStepPeel.same] using andRight h) (projectionValue 1 xs)

def queries : Fin 14 → Program 3 :=
 ![frontOf (.projection 2),firstOf (.projection 2),secondOf (.projection 2),tailOf (.projection 2),
   leftOf (firstOf (.projection 2)),rightOf (firstOf (.projection 2)),
   leftOf (secondOf (.projection 2)),rightOf (secondOf (.projection 2)),
   rawCons (secondOf (.projection 2)) (tailOf (.projection 2)),
   rawCons (firstOf (.projection 2)) (tailOf (.projection 2)),sourceSuffix,targetSuffix,
   payloadOf (.projection 2),restOf (.projection 2)]

def facts (source target certificate : OTerm alpha) (v : Fin 14 → OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing certificate (v 0) (v 12) ⊓
 (graph2 InternalPairing.pairing (v 12) (v 1) (v 13) ⊓
 (graph2 InternalPairing.pairing (v 13) (v 2) (v 3) ⊓
 (graph2 InternalPairing.pairing (v 1) (v 4) (v 5) ⊓
 (graph2 InternalPairing.pairing (v 2) (v 6) (v 7) ⊓
 (OriginalTypedArgumentObservationSwapDefinitions.Geometry (v 4) (v 6) (v 5) (v 7) (v 3) (v 8) (v 9) (v 10) (v 11) ⊓
 (graph2 OriginalTypedArgumentPrefixBuilder.build source (v 0) (v 10) ⊓
  graph2 OriginalTypedArgumentPrefixBuilder.build target (v 0) (v 11)))))))

theorem atValues (source target certificate : OTerm alpha) (v : Fin 14 → OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edge (suc z) source target certificate)))
 (hq : ∀ i : Fin 14, Nonempty (Derivation body Delta (programGraph (queries i) (v i)
   (Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0)))))) :
 Nonempty (Derivation body Delta (facts source target certificate v)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0))
 have h0 : Nonempty (Derivation body Delta (programGraph (frontOf (.projection 2)) (v 0) xs)) := hq 0
 have h1 : Nonempty (Derivation body Delta (programGraph (firstOf (.projection 2)) (v 1) xs)) := hq 1
 have h2 : Nonempty (Derivation body Delta (programGraph (secondOf (.projection 2)) (v 2) xs)) := hq 2
 have h3 : Nonempty (Derivation body Delta (programGraph (tailOf (.projection 2)) (v 3) xs)) := hq 3
 have h4 : Nonempty (Derivation body Delta (programGraph (leftOf (firstOf (.projection 2))) (v 4) xs)) := hq 4
 have h5 : Nonempty (Derivation body Delta (programGraph (rightOf (firstOf (.projection 2))) (v 5) xs)) := hq 5
 have h6 : Nonempty (Derivation body Delta (programGraph (leftOf (secondOf (.projection 2))) (v 6) xs)) := hq 6
 have h7 : Nonempty (Derivation body Delta (programGraph (rightOf (secondOf (.projection 2))) (v 7) xs)) := hq 7
 have h8 : Nonempty (Derivation body Delta (programGraph (rawCons (secondOf (.projection 2)) (tailOf (.projection 2))) (v 8) xs)) := hq 8
 have h9 : Nonempty (Derivation body Delta (programGraph (rawCons (firstOf (.projection 2)) (tailOf (.projection 2))) (v 9) xs)) := hq 9
 have h10 : Nonempty (Derivation body Delta (programGraph (sourceSuffix) (v 10) xs)) := hq 10
 have h11 : Nonempty (Derivation body Delta (programGraph (targetSuffix) (v 11) xs)) := hq 11
 have h12 : Nonempty (Derivation body Delta (programGraph (payloadOf (.projection 2)) (v 12) xs)) := hq 12
 have h13 : Nonempty (Derivation body Delta (programGraph (restOf (.projection 2)) (v 13) xs)) := hq 13
 have hcert : Nonempty (Derivation body Delta (programGraph (.projection 2) certificate xs)) := projectionValue 2 xs
 have lc := unaryRecover InternalUnpair.left (.projection 2) (v 0) certificate xs h0 hcert
 have rc := unaryRecover InternalUnpair.right (.projection 2) (v 12) certificate xs h12 hcert
 have lp := unaryRecover InternalUnpair.left (payloadOf (.projection 2)) (v 1) (v 12) xs h1 h12
 have rp := unaryRecover InternalUnpair.right (payloadOf (.projection 2)) (v 13) (v 12) xs h13 h12
 have lr := unaryRecover InternalUnpair.left (restOf (.projection 2)) (v 2) (v 13) xs h2 h13
 have rr := unaryRecover InternalUnpair.right (restOf (.projection 2)) (v 3) (v 13) xs h3 h13
 have lq := unaryRecover InternalUnpair.left (firstOf (.projection 2)) (v 4) (v 1) xs h4 h1
 have rq := unaryRecover InternalUnpair.right (firstOf (.projection 2)) (v 5) (v 1) xs h5 h1
 have ls := unaryRecover InternalUnpair.left (secondOf (.projection 2)) (v 6) (v 2) xs h6 h2
 have rs := unaryRecover InternalUnpair.right (secondOf (.projection 2)) (v 7) (v 2) xs h7 h2
 have pc := closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body alpha certificate (v 0) (v 12)) (andIntro lc rc)
 have pp := closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body alpha (v 12) (v 1) (v 13)) (andIntro lp rp)
 have pr := closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body alpha (v 13) (v 2) (v 3)) (andIntro lr rr)
 have pq := closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body alpha (v 1) (v 4) (v 5)) (andIntro lq rq)
 have ps := closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body alpha (v 2) (v 6) (v 7)) (andIntro ls rs)
 have cy := ternaryRecover OriginalRawSyntaxTransport.consConstructor (leftOf (secondOf (.projection 2)))
   (rightOf (secondOf (.projection 2))) (tailOf (.projection 2)) (v 8) (v 6) (v 7) (v 3) xs h8 h6 h7 h3
 have cx := ternaryRecover OriginalRawSyntaxTransport.consConstructor (leftOf (firstOf (.projection 2)))
   (rightOf (firstOf (.projection 2))) (tailOf (.projection 2)) (v 9) (v 4) (v 5) (v 3) xs h9 h4 h5 h3
 have cxy := ternaryRecover OriginalRawSyntaxTransport.consConstructor (leftOf (firstOf (.projection 2)))
   (rightOf (firstOf (.projection 2))) (rawCons (secondOf (.projection 2)) (tailOf (.projection 2))) (v 10) (v 4) (v 5) (v 8) xs
   (by simpa only [sourceSuffix,rawCons] using h10) h4 h5 h8
 have cyx := ternaryRecover OriginalRawSyntaxTransport.consConstructor (leftOf (secondOf (.projection 2)))
   (rightOf (secondOf (.projection 2))) (rawCons (firstOf (.projection 2)) (tailOf (.projection 2))) (v 11) (v 6) (v 7) (v 9) xs
   (by simpa only [targetSuffix,rawCons] using h11) h6 h7 h9
 obtain ⟨es,et⟩ := endpointsAt source target certificate he
 have bs := binaryRecover OriginalTypedArgumentPrefixBuilder.build (frontOf (.projection 2)) sourceSuffix source (v 0) (v 10) xs
   (by simpa only [sourceEndpoint] using es) h0 h10
 have bt := binaryRecover OriginalTypedArgumentPrefixBuilder.build (frontOf (.projection 2)) targetSuffix target (v 0) (v 11) xs
   (by simpa only [targetEndpoint] using et) h0 h11
 exact andIntro pc (andIntro pp (andIntro pr (andIntro pq (andIntro ps
   (andIntro (andIntro cy (andIntro cxy (andIntro cx cyx))) (andIntro bs bt))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeRawProof
