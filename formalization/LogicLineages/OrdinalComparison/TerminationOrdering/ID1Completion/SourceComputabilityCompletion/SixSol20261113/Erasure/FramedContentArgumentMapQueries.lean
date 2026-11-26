module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentRows
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProducedLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentMapQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open InternalTagArithmeticSyntaxProof (suc)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime FramedContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fromMetadata (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged size count value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs))) :
 Nonempty (Derivation body Delta (Content R job value)) := by
 let mp : Program 1 := InternalListMap.map (k := 0) (contentProgram R)
 let rp : Program 1 := .composition OriginalTypedArgumentObservations.reverse (fun _ : Fin 1 => mp)
 let qs : Fin 2 → Program 1 := ![mp,rp]
 let xs : Fin 1 → OTerm alpha := Fin.cons jobs Fin.elim0
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hinc hg
 let xx : Fin 1 → OTerm beta := Fin.cons (jobs.relabel j) Fin.elim0
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hg
 have hj' := renameInto hj j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hadm' := renameInto hadm j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hpay' := renameInto hpay j Theta hinc
 have hframe' := renameInto hframe j Theta hinc
 have he' := renameInto he j Theta hinc
 have htag' := renameInto htag j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hsize' := renameInto hsize j Theta hinc
 have hall' := renameInto hall j Theta hinc
 have hcontent' := renameInto hcontent j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,admissibleRename,
   OriginalContextInsertionSyntaxProof.lengthRename,JobFrameSyntax.frameRename,
   VisitListCompletionSyntax.allRename,ContentVisitsSyntax.allRename] at hj' ht' hr' hp' hadm' ha' hl' hc' hpay' hframe' he' htag' hf' hsize' hall' hcontent'
 have hrev := unaryRecover OriginalTypedArgumentObservations.reverse mp
   (ys 1) (ys 0) xx (hg 1) (hg 0)
 simp only [Content,graph1Rename]
 exact FramedContentArgumentRows.fromRows R H M W
   (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (returnFrame.relabel j) (jobs.relabel j) (tagged.relabel j) (ys 0) (ys 1) (size.relabel j) (count.relabel j) (value.relabel j)
   hj' ht' hr' hp' hadm' ha' hl' hc' hpay' hframe' he' htag' (hg 0) hrev hf' hsize' hall' hcontent'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentMapQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentMapQueries
