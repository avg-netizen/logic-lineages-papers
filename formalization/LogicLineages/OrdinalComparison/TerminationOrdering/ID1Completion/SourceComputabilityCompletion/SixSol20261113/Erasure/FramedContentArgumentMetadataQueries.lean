module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentMapQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentMetadataQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime FramedContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem withTagged (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma jobs size children deletions counts payload returnFrame count value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)))
 : Nonempty (Derivation body Delta (Content R job value)) := by
 apply programCases OriginalHereditaryVisitScheduler.tagVisits (Fin.cons jobs Fin.elim0) _
 intro beta j Theta tagged hi hq
 simp only [Content,graph1Rename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have hcontent' := renameInto hcontent j Theta hi
 have hf' := renameInto hf j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 have hpay' := renameInto hpay j Theta hi
 have hframe' := renameInto hframe j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,ContentVisitsSyntax.allRename,JobFrameSyntax.frameRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' ha' hl' hc' hpay' hframe'
 exact FramedContentArgumentMapQueries.fromMetadata R H M W (job.relabel j) (typed.relabel j) (rawJob.relabel j)
   (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (children.relabel j) (deletions.relabel j)
   (counts.relabel j) (payload.relabel j) (returnFrame.relabel j) (jobs.relabel j) tagged (size.relabel j)
   (count.relabel j) (value.relabel j)
   hj' ht' hr' hp' hadm' ha' hl' hc' hpay' hframe' he' hq hf' hsize' hall' hcontent'
theorem withReturnFrame (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma jobs size children deletions counts payload count value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 : Nonempty (Derivation body Delta (Content R job value)) := by
 apply programCases InternalPairing.pairing (Fin.cons (numeral 1) (Fin.cons payload Fin.elim0)) _
 intro beta j Theta returnFrame hi hq
 simp only [Content,graph1Rename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have hcontent' := renameInto hcontent j Theta hi
 have hf' := renameInto hf j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 have hpay' := renameInto hpay j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,ContentVisitsSyntax.allRename,JobFrameSyntax.frameRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' ha' hl' hc' hpay'
 exact withTagged R H M W (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) returnFrame (count.relabel j) (value.relabel j)
   hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' ha' hl' hc' hpay' hq
theorem withPayload (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma jobs size children deletions counts count value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 : Nonempty (Derivation body Delta (Content R job value)) := by
 apply programCases InternalPairing.pairing (Fin.cons job (Fin.cons counts Fin.elim0)) _
 intro beta j Theta payload hi hq
 simp only [Content,graph1Rename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have hcontent' := renameInto hcontent j Theta hi
 have hf' := renameInto hf j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,ContentVisitsSyntax.allRename,JobFrameSyntax.frameRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' ha' hl' hc'
 exact withReturnFrame R H M W (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) payload (count.relabel j) (value.relabel j)
   hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' ha' hl' hc' hq
theorem withCounts (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma jobs size children deletions count value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length deletions gamma)))
 : Nonempty (Derivation body Delta (Content R job value)) := by
 apply programCases InternalPairing.pairing (Fin.cons children (Fin.cons deletions Fin.elim0)) _
 intro beta j Theta counts hi hq
 simp only [Content,graph1Rename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have hcontent' := renameInto hcontent j Theta hi
 have hf' := renameInto hf j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,ContentVisitsSyntax.allRename,JobFrameSyntax.frameRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' ha' hl'
 exact withPayload R H M W (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) (children.relabel j) (deletions.relabel j) counts (count.relabel j) (value.relabel j)
   hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' ha' hl' hq
theorem withDeletions (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma jobs size children count value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 : Nonempty (Derivation body Delta (Content R job value)) := by
 apply programCases OriginalContextInsertion.length (Fin.cons gamma Fin.elim0) _
 intro beta j Theta deletions hi hq
 simp only [Content,graph1Rename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have hcontent' := renameInto hcontent j Theta hi
 have hf' := renameInto hf j Theta hi
 have ha' := renameInto ha j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,ContentVisitsSyntax.allRename,JobFrameSyntax.frameRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' ha'
 exact withCounts R H M W (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) (children.relabel j) deletions (count.relabel j) (value.relabel j)
   hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' ha' hq
theorem fromFields (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma jobs size count value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 : Nonempty (Derivation body Delta (Content R job value)) := by
 apply programCases (OriginalRawSyntaxTransport.arityOf (.projection 0)) (Fin.cons raw Fin.elim0) _
 intro beta j Theta children hi hq
 simp only [Content,graph1Rename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have hcontent' := renameInto hcontent j Theta hi
 have hf' := renameInto hf j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,ContentVisitsSyntax.allRename,JobFrameSyntax.frameRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf'
 exact withDeletions R H M W (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) children (count.relabel j) (value.relabel j)
   hj' ht' hr' hp' hadm' he' hsize' hall' hcontent' hf' hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentMetadataQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentMetadataQueries
