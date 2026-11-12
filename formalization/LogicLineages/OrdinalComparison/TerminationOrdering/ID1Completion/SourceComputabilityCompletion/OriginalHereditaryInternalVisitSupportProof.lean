module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem workGraph (input work results : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedVisit.work work input)) := by
 let xs : Fin 1 → OTerm alpha := ![input]
 exact unaryValue InternalUnpair.left (.projection 0) work input xs (pairLeft input work results hs) (projectionValue 0 xs)
theorem resultsGraph (input work results : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedVisit.results results input)) := by
 let xs : Fin 1 → OTerm alpha := ![input]
 exact unaryValue InternalUnpair.right (.projection 0) results input xs (pairRight input work results hs) (projectionValue 0 xs)
theorem frameGraph (input work results visit rest : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit rest))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedVisit.frame visit input)) :=
 unaryValue InternalListCodec.headCode OriginalHereditaryAnnotatedVisit.work visit work ![input]
  (InternalRawListRecursionSupportProof.consHead work visit rest hw) (workGraph input work results hs)
theorem restGraph (input work results visit rest : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit rest))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedVisit.rest rest input)) :=
 unaryValue InternalListCodec.tailCode OriginalHereditaryAnnotatedVisit.work rest work ![input]
  (InternalRawListRecursionSupportProof.consTail work visit rest hw) (workGraph input work results hs)
theorem parentGraph (input work results visit rest parent : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit rest)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) parent))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedVisit.parent parent input)) :=
 unaryValue InternalUnpair.right OriginalHereditaryAnnotatedVisit.frame parent visit ![input]
  (pairRight visit (numeral 0) parent hv) (frameGraph input work results visit rest hs hw)

theorem control (R : Program 2) (input work results visit rest parent out : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit rest)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) parent)))
 (hbody : Nonempty (Derivation body Delta (graph1
   (pairOf OriginalHereditaryAnnotatedVisit.scheduled OriginalHereditaryAnnotatedVisit.results) out input))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) out input)) := by
 let xs : Fin 1 → OTerm alpha := ![input]
 have hwork := workGraph input work results hs
 have hframe := frameGraph input work results visit rest hs hw
 have htag : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryAnnotatedVisit.frame) (numeral 0) input)) :=
  unaryValue InternalUnpair.left OriginalHereditaryAnnotatedVisit.frame (numeral 0) visit xs
   (pairLeft visit (numeral 0) parent hv) hframe
 have hn := OriginalTypedDecoderInternalListProof.consNonzero work visit rest hw
 have hvis : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedVisit.step out input)) := by
  apply InternalApplicationResultStackReturnSupportProof.nonzeroBranchIntro
   OriginalHereditaryAnnotatedVisit.work (.projection 0) _ out work xs hwork hn
  exact InternalAcceptanceBranchProof.zeroBranchIntro (leftOf OriginalHereditaryAnnotatedVisit.frame)
   (pairOf OriginalHereditaryAnnotatedVisit.scheduled OriginalHereditaryAnnotatedVisit.results) (.projection 0) out xs htag hbody
 apply InternalApplicationResultStackReturnSupportProof.nonzeroBranchIntro
  OriginalHereditaryCombinedStep.work (.projection 0) _ out work xs hwork hn
 exact sameYesIntro (leftOf OriginalHereditaryCombinedStep.frame) (OriginalRawSyntaxTransport.constant 1 0)
  OriginalHereditaryAnnotatedVisit.step _ out (numeral 0) (numeral 0) xs htag (constantValue 0 xs)
  (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 0)))) hvis
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitSupportProof
