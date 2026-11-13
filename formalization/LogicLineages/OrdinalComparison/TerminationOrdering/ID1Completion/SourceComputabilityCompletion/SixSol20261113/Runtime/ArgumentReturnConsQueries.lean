module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnAtValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnConsQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
theorem atConstructor (R Q : Program 2) (job typed rawJob raw parameter children deletions counts payload frame produced first second row packed rawPayload value : OTerm alpha)
 (domain child tailRaw rawJobs annotatedPrefix childRow : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed (numeral 0) raw)))
 (hf : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)))
 (hcon : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw domain child tailRaw)))
 (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)))
 (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix children (numeral 1) (numeral 0) raw rawJobs)))
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q)) childRow annotatedPrefix)))
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph children childRow)))
 (hfirst : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first (numeral 0) childRow)))
 (hsecond : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) childRow)))
 (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hs : UniformReturnSupplierProof.Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) value raw parameter)) := by
 apply programCases OriginalHereditaryReturn.returnArgumentsCons (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) _
 intro beta j Theta returned hi hret
 simp only [consTermRename,emptyRename] at hret
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hframe' := renameInto hframe j Theta hi
 have hpacked' := renameInto hpacked j Theta hi
 have hf' := renameInto hf j Theta hi
 have htag' := renameInto htag j Theta hi
 have hcon' := renameInto hcon j Theta hi
 have he' := renameInto he j Theta hi
 have hscan' := renameInto hscan j Theta hi
 have hm' := renameInto hm j Theta hi
 have hlen' := renameInto hlen j Theta hi
 have hfirst' := renameInto hfirst j Theta hi
 have hsecond' := renameInto hsecond j Theta hi
 have harity' := renameInto harity j Theta hi
 simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,numeralRename,UniformReturnSyntax.frameRename,OriginalContextInsertionSyntaxProof.lengthRename] at hj' ht' hr' hc' hp' hframe' hpacked' hf' htag' hcon' he' hscan' hm' hlen' hfirst' hsecond' harity'
 have hs' := UniformReturnSupplierProof.supplierRename j Theta children deletions produced first second row hi hs
 rw [graph2Rename]
 exact ArgumentReturnAtValuesProof.consAtValue R Q (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) (packed.relabel j) (rawPayload.relabel j) (value.relabel j) (domain.relabel j) (child.relabel j) (tailRaw.relabel j) (rawJobs.relabel j) (annotatedPrefix.relabel j) (childRow.relabel j) returned hj' ht' hr' hc' hp' hframe' hpacked' hf' htag' hcon' he' hscan' hm' hlen' hfirst' hsecond' hret harity' hs'
theorem cons (R Q : Program 2) (job typed rawJob raw parameter children deletions counts payload frame produced first second row packed rawPayload value : OTerm alpha)
 (rawJobs annotatedPrefix childRow : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed (numeral 0) raw)))
 (hf : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)))
 (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)))
 (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix children (numeral 1) (numeral 0) raw rawJobs)))
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q)) childRow annotatedPrefix)))
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph children childRow)))
 (hfirst : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first (numeral 0) childRow)))
 (hsecond : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) childRow)))
 (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hs : UniformReturnSupplierProof.Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) value raw parameter)) := by
 have htagGraph := pairLeft raw (numeral 7) rawPayload htag
 apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ htagGraph
 intro beta j Theta domain child tailRaw hi hcon
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hframe' := renameInto hframe j Theta hi
 have hpacked' := renameInto hpacked j Theta hi
 have hf' := renameInto hf j Theta hi
 have htag' := renameInto htag j Theta hi
 have he' := renameInto he j Theta hi
 have hscan' := renameInto hscan j Theta hi
 have hm' := renameInto hm j Theta hi
 have hlen' := renameInto hlen j Theta hi
 have hfirst' := renameInto hfirst j Theta hi
 have hsecond' := renameInto hsecond j Theta hi
 have harity' := renameInto harity j Theta hi
 simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,numeralRename,UniformReturnSyntax.frameRename,OriginalContextInsertionSyntaxProof.lengthRename] at hj' ht' hr' hc' hp' hframe' hpacked' hf' htag' he' hscan' hm' hlen' hfirst' hsecond' harity'
 have hs' := UniformReturnSupplierProof.supplierRename j Theta children deletions produced first second row hi hs
 rw [graph2Rename]
 exact atConstructor R Q (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) (packed.relabel j) (rawPayload.relabel j) (value.relabel j) domain child tailRaw (rawJobs.relabel j) (annotatedPrefix.relabel j) (childRow.relabel j) hj' ht' hr' hc' hp' hframe' hpacked' hf' htag' hcon he' hscan' hm' hlen' hfirst' hsecond' harity' hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnConsQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnConsQueries
