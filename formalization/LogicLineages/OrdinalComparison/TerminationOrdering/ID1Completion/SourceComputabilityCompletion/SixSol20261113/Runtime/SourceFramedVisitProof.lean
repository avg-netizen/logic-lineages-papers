module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedVisitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof (arityValueAt)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph OriginalHereditaryAnnotatedExpansion.expansion OriginalHereditaryAnnotatedVisit.step
/-- Actual visit with all metadata fixed independently of the arbitrary old
results and agenda suffix. The original dispatcher is executed literally. -/
theorem visitStep (R : Program 2)
 (job role typed typ rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged
  input work old visit suffix returnRest next output : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work old)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit suffix)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) job)))
 (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode returnRest returnFrame suffix)))
 (hnext : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append next tagged returnRest)))
 (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output next old)))
 : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) output input)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hparent := OriginalHereditaryInternalVisitSupportProof.parentGraph input work old visit suffix job hi hw hv
 have htyped := unaryValue InternalUnpair.right OriginalHereditaryAnnotatedVisit.parent typed job xs
   (pairRight job role typed hj) hparent
 have hrawJob := unaryValue InternalUnpair.right (rightOf OriginalHereditaryAnnotatedVisit.parent) rawJob typed xs
   (pairRight typed typ rawJob ht) htyped
 have hraw := unaryValue InternalUnpair.left OriginalHereditaryAnnotatedVisit.rawJob raw rawJob xs
   (pairLeft rawJob raw parameter hr) hrawJob
 have hparameter := unaryValue InternalUnpair.right OriginalHereditaryAnnotatedVisit.rawJob parameter rawJob xs
   (pairRight rawJob raw parameter hr) hrawJob
 have hgamma := unaryValue InternalUnpair.right OriginalHereditaryAnnotatedVisit.parameter gamma parameter xs
   (pairRight parameter c gamma hp) hparameter
 have hchildren := arityValueAt OriginalHereditaryAnnotatedVisit.raw children raw xs hraw ha
 let delProgram : Program 1 := .composition OriginalContextInsertion.length
   (fun _ : Fin 1 => rightOf OriginalHereditaryAnnotatedVisit.parameter)
 have hdeletions := unaryValue OriginalContextInsertion.length
   (rightOf OriginalHereditaryAnnotatedVisit.parameter) deletions gamma xs hl hgamma
 let countsProgram := pairOf (OriginalRawSyntaxTransport.arityOf OriginalHereditaryAnnotatedVisit.raw) delProgram
 have hcounts := binaryValue InternalPairing.pairing
   (OriginalRawSyntaxTransport.arityOf OriginalHereditaryAnnotatedVisit.raw) delProgram
   counts children deletions xs hc hchildren hdeletions
 have hpayload := binaryValue InternalPairing.pairing OriginalHereditaryAnnotatedVisit.parent countsProgram
   payload job counts xs hpay hparent hcounts
 have hreturn := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 1)
   (pairOf OriginalHereditaryAnnotatedVisit.parent countsProgram) returnFrame (numeral 1) payload xs
   hframe (constantValue 1 xs) hpayload
 have hexpanded := unaryValue OriginalHereditaryAnnotatedExpansion.expansion OriginalHereditaryAnnotatedVisit.parent
   jobs job xs he hparent
 have htagged := unaryValue OriginalHereditaryVisitScheduler.tagVisits OriginalHereditaryAnnotatedVisit.expanded
   tagged jobs xs htag hexpanded
 have hsuffix := OriginalHereditaryInternalVisitSupportProof.restGraph input work old visit suffix hi hw
 have hreturnRest := binaryValue InternalListCodec.consCode OriginalHereditaryAnnotatedVisit.returnFrame
   OriginalHereditaryAnnotatedVisit.rest returnRest returnFrame suffix xs hrest hreturn hsuffix
 have hscheduled := binaryValue InternalApplicationValidityStackAppend.append
   (.composition OriginalHereditaryVisitScheduler.tagVisits (fun _ : Fin 1 => OriginalHereditaryAnnotatedVisit.expanded))
   (consOf OriginalHereditaryAnnotatedVisit.returnFrame OriginalHereditaryAnnotatedVisit.rest)
   next tagged returnRest xs hnext htagged hreturnRest
 have hbody := binaryValue InternalPairing.pairing OriginalHereditaryAnnotatedVisit.scheduled
   OriginalHereditaryAnnotatedVisit.results output next old xs hout hscheduled
   (OriginalHereditaryInternalVisitSupportProof.resultsGraph input work old hi)
 exact OriginalHereditaryInternalVisitSupportProof.control R input work old visit suffix job output hi hw hv hbody
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedVisitProof
