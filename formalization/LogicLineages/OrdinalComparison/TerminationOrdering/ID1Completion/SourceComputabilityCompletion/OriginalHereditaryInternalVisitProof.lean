module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport (arityOf constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalHereditaryInternalVisitSupportProof

theorem visitCases : OriginalHereditaryInternalVisitTargets.VisitCases := by
 intro R body alpha Delta input work results visit rest parent jobs psi hs hw hv he next
 let a : Program 1 := arityOf OriginalHereditaryAnnotatedVisit.raw
 let d : Program 1 := .composition OriginalContextInsertion.length
  (fun _ : Fin 1 => rightOf OriginalHereditaryAnnotatedVisit.parameter)
 let counts : Program 1 := pairOf a d
 let payload : Program 1 := pairOf OriginalHereditaryAnnotatedVisit.parent counts
 let tagged : Program 1 := .composition OriginalHereditaryVisitScheduler.tagVisits
  (fun _ : Fin 1 => OriginalHereditaryAnnotatedVisit.expanded)
 let returnRest : Program 1 := consOf OriginalHereditaryAnnotatedVisit.returnFrame OriginalHereditaryAnnotatedVisit.rest
 let out : Program 1 := pairOf OriginalHereditaryAnnotatedVisit.scheduled OriginalHereditaryAnnotatedVisit.results
 let qs : Fin 9 → Program 1 := ![a,d,counts,payload,OriginalHereditaryAnnotatedVisit.returnFrame,tagged,returnRest,OriginalHereditaryAnnotatedVisit.scheduled,out]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs (Fin.cons input Fin.elim0) psi
 intro beta j Theta ys hinc hq
 simp only [consTermRename,emptyRename] at hq
 let xx : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
 have hs' := renameInto hs j Theta hinc
 have hw' := renameInto hw j Theta hinc
 have hv' := renameInto hv j Theta hinc
 have he' := renameInto he j Theta hinc
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs' hw' hv' he'
 have hparent := parentGraph (input.relabel j) (work.relabel j) (results.relabel j) (visit.relabel j) (rest.relabel j) (parent.relabel j) hs' hw' hv'
 have hrest := restGraph (input.relabel j) (work.relabel j) (results.relabel j) (visit.relabel j) (rest.relabel j) hs' hw'
 have hresults := resultsGraph (input.relabel j) (work.relabel j) (results.relabel j) hs'
 have hexp : Nonempty (Derivation body Theta (graph1 OriginalHereditaryAnnotatedVisit.expanded (jobs.relabel j) (input.relabel j))) :=
  unaryValue OriginalHereditaryAnnotatedExpansion.expansion OriginalHereditaryAnnotatedVisit.parent (jobs.relabel j) (parent.relabel j) xx he' hparent
 have hcounts := binaryRecover InternalPairing.pairing a d (ys 2) (ys 0) (ys 1) xx (hq 2) (hq 0) (hq 1)
 have hpayload := binaryRecover InternalPairing.pairing OriginalHereditaryAnnotatedVisit.parent counts (ys 3) (parent.relabel j) (ys 2) xx (hq 3) hparent (hq 2)
 have hreturn := binaryRecover InternalPairing.pairing (constant 1 1) payload (ys 4) (numeral 1) (ys 3) xx (hq 4) (constantValue 1 xx) (hq 3)
 have htagged := unaryRecover OriginalHereditaryVisitScheduler.tagVisits OriginalHereditaryAnnotatedVisit.expanded (ys 5) (jobs.relabel j) xx (hq 5) hexp
 have hreturnRest := binaryRecover InternalListCodec.consCode OriginalHereditaryAnnotatedVisit.returnFrame OriginalHereditaryAnnotatedVisit.rest
  (ys 6) (ys 4) (rest.relabel j) xx (hq 6) (hq 4) hrest
 have hscheduled := binaryRecover InternalApplicationValidityStackAppend.append tagged returnRest (ys 7) (ys 5) (ys 6) xx (hq 7) (hq 5) (hq 6)
 have hout := binaryRecover InternalPairing.pairing OriginalHereditaryAnnotatedVisit.scheduled OriginalHereditaryAnnotatedVisit.results
  (ys 8) (ys 7) (results.relabel j) xx (hq 8) (hq 7) hresults
 have hstep := control R (input.relabel j) (work.relabel j) (results.relabel j) (visit.relabel j) (rest.relabel j) (parent.relabel j) (ys 8) hs' hw' hv' (hq 8)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) hinc
  (hq 0) (hq 1) hcounts hpayload hreturn htagged hreturnRest hscheduled hout hstep
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitProof
