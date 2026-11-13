module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedLocalCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedLocalQueries
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem withTagged (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter c gamma jobs size children deletions counts payload returnFrame : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 apply programCases OriginalHereditaryVisitScheduler.tagVisits (Fin.cons jobs Fin.elim0) _
 intro beta j Theta tagged hi hq
 rw [JobCompletionSyntax.completionRename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 have hpay' := renameInto hpay j Theta hi
 have hframe' := renameInto hframe j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' ha' hl' hc' hpay' hframe'
 exact SourceFramedLocalCore.fromMetadata R H M W (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (returnFrame.relabel j) (jobs.relabel j) tagged (size.relabel j)
   hj' ht' hr' hp' ha' hl' hc' hpay' hframe' he' hq hadm' hsize' hall'
theorem withReturnFrame (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter c gamma jobs size children deletions counts payload : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 apply programCases InternalPairing.pairing (Fin.cons (numeral 1) (Fin.cons payload Fin.elim0)) _
 intro beta j Theta returnFrame hi hq
 rw [JobCompletionSyntax.completionRename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 have hpay' := renameInto hpay j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' ha' hl' hc' hpay'
 exact withTagged R H M W (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) returnFrame
   hj' ht' hr' hp' hadm' he' hsize' hall' ha' hl' hc' hpay' hq
theorem withPayload (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter c gamma jobs size children deletions counts : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 apply programCases InternalPairing.pairing (Fin.cons job (Fin.cons counts Fin.elim0)) _
 intro beta j Theta payload hi hq
 rw [JobCompletionSyntax.completionRename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' ha' hl' hc'
 exact withReturnFrame R H M W (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) payload
   hj' ht' hr' hp' hadm' he' hsize' hall' ha' hl' hc' hq
theorem withCounts (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter c gamma jobs size children deletions : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length deletions gamma)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 apply programCases InternalPairing.pairing (Fin.cons children (Fin.cons deletions Fin.elim0)) _
 intro beta j Theta counts hi hq
 rw [JobCompletionSyntax.completionRename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' ha' hl'
 exact withPayload R H M W (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) (children.relabel j) (deletions.relabel j) counts
   hj' ht' hr' hp' hadm' he' hsize' hall' ha' hl' hq
theorem withDeletions (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter c gamma jobs size children : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 apply programCases OriginalContextInsertion.length (Fin.cons gamma Fin.elim0) _
 intro beta j Theta deletions hi hq
 rw [JobCompletionSyntax.completionRename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 have ha' := renameInto ha j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall' ha'
 exact withCounts R H M W (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) (children.relabel j) deletions
   hj' ht' hr' hp' hadm' he' hsize' hall' ha' hq
theorem fromFields (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter c gamma jobs size : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 apply programCases (OriginalRawSyntaxTransport.arityOf (.projection 0)) (Fin.cons raw Fin.elim0) _
 intro beta j Theta children hi hq
 rw [JobCompletionSyntax.completionRename]
 simp only [consTermRename,emptyRename,numeralRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,admissibleRename] at hj' ht' hr' hp' hadm' he' hsize' hall'
 exact withDeletions R H M W (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (jobs.relabel j) (size.relabel j) children
   hj' ht' hr' hp' hadm' he' hsize' hall' hq
theorem actualLocalCompletion : SourceFramedTargets.ActualLocalCompletion := by
 intro R H M W body alpha Delta c B job jobs size hj he hsize hall
 apply OriginalHereditaryInternalAgendaBindingProof.jobCases H M W c B job _ hj
 intro beta j Theta role typ typed rawJob raw parameter gamma weight hi hf
 rw [JobCompletionSyntax.completionRename]
 have he' := renameInto he j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 simp only [graph1Rename,OriginalContextInsertionSyntaxProof.lengthRename,VisitListCompletionSyntax.allRename] at he' hsize' hall'
 exact fromFields R H M W (job.relabel j) role typed typ rawJob raw parameter (c.relabel j) gamma
   (jobs.relabel j) (size.relabel j)
   (andLeft hf) (andLeft (andRight hf)) (andLeft (andRight (andRight hf)))
   (andLeft (andRight (andRight (andRight hf))))
   (andLeft (andRight (andRight (andRight (andRight hf))))) he' hsize' hall'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedLocalQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedLocalQueries
