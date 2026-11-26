module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEvaluatorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomFuelProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEvaluatorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualEvaluator : OriginalInternalBottomEvaluatorTargets.ActualEvaluator := by
 intro R body alpha Delta raw typ packed c parameter rawJob typed job visitFrame work input counts payload frame returnWork middle root tail value stack output fuel
   hb hpacked hp hr ht hj hv hs hc hpay hf hm htail hvalue hout hw hret hstack hroot hFuel
 have hrun := OriginalInternalBottomFuelProof.actualFuel R body alpha Delta raw typ packed c parameter rawJob typed job visitFrame work input counts payload frame returnWork middle root tail value stack output fuel
   hb hpacked hp hr ht hj hv hs hc hpay hf hm htail hvalue hout hw hret hstack hroot hFuel
 let xs : Fin 2 → OTerm alpha := Fin.cons packed (Fin.cons parameter Fin.elim0)
 have htyp := unaryValue InternalUnpair.left (.projection 0) typ packed xs (pairLeft packed typ raw hpacked) (projectionValue 0 xs)
 have hraw := unaryValue InternalUnpair.right (.projection 0) raw packed xs (pairRight packed typ raw hpacked) (projectionValue 0 xs)
 have hrawJob := binaryValue InternalPairing.pairing (rightOf (.projection 0)) (.projection 1) rawJob raw parameter xs hr hraw (projectionValue 1 xs)
 have htyped := binaryValue InternalPairing.pairing (leftOf (.projection 0)) (pairOf (rightOf (.projection 0)) (.projection 1)) typed typ rawJob xs ht htyp hrawJob
 have hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryEvaluatorDefinitions.job job packed parameter)) :=
   binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) _ job z typed xs hj (constantValue 0 xs) htyped
 have hvisit := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) OriginalHereditaryEvaluatorDefinitions.job visitFrame z job xs hv (constantValue 0 xs) hjob
 have hwork := binaryValue InternalListCodec.consCode (pairOf (OriginalRawSyntaxTransport.constant 2 0) OriginalHereditaryEvaluatorDefinitions.job)
   (OriginalRawSyntaxTransport.constant 2 0) work visitFrame z xs hw hvisit (constantValue 0 xs)
 have hinitial : Nonempty (Derivation body Delta (graph2 OriginalHereditaryEvaluatorDefinitions.initial input packed parameter)) :=
   binaryValue InternalPairing.pairing _ (OriginalRawSyntaxTransport.constant 2 0) input work z xs hs hwork (constantValue 0 xs)
 have hcomputed := unaryValue OriginalHereditaryFuelProgram.fuel OriginalHereditaryEvaluatorDefinitions.job fuel job xs hFuel hjob
 exact OriginalHereditaryEvaluatorInternalProof.runProjection R body alpha Delta packed parameter fuel input output z stack value
   hcomputed hinitial hrun hout (InternalRawListRecursionSupportProof.consHead stack value z hstack)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEvaluatorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEvaluatorProof
