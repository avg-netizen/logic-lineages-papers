module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobCompletionSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedLocalCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fromReturn (R : Program 2)
 (job role typed typ rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged count produced : OTerm alpha)
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
 (hprefix : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged count produced)))
 (hreturn : Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R returnFrame produced))) :
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 apply UniformReturnCompletionSyntax.completionCases R returnFrame produced _ hreturn
 intro beta j Theta value hi hv
 rw [JobCompletionSyntax.completionRename]
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 have hpay' := renameInto hpay j Theta hi
 have hframe' := renameInto hframe j Theta hi
 have he' := renameInto he j Theta hi
 have htag' := renameInto htag j Theta hi
 have hprefix' := renameInto hprefix j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   PrefixFrameSyntax.frameRename] at hj' ht' hr' hp' ha' hl' hc' hpay' hframe' he' htag' hprefix'
 exact JobCompletionSyntax.completionIntro R (job.relabel j) (suc (add (count.relabel j) (suc (numeral 0)))) value
   (SourceFramedRunProof.framed R (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (returnFrame.relabel j) (jobs.relabel j) (tagged.relabel j) (count.relabel j) (produced.relabel j) value
     hj' ht' hr' hp' ha' hl' hc' hpay' hframe' he' htag' hprefix' hv)
theorem fromChildren (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged count produced size : OTerm alpha)
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
 (hprefix : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged count produced)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hproduced : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size produced))) :
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 have hexact := SourceFramedExpansionLengthProof.actualLength job role typ typed rawJob raw parameter gamma c children deletions jobs
   hj ht hr hp ha hl he
 have heq := valueUnique OriginalContextInsertion.length size (add children deletions) (Fin.cons jobs Fin.elim0) hsize hexact
 have hlen := outputTransport OriginalContextInsertion.length size (add children deletions) (Fin.cons produced Fin.elim0) heq hproduced
 have hreturn := UniformReturnProof.actualUniformReturn R H M W body alpha Delta
   job role typ typed rawJob raw parameter gamma c children deletions counts payload returnFrame produced
   hj ht hr hp hadm ha hl hc hpay hframe hlen
 exact fromReturn R job role typed typ rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged count produced
   hj ht hr hp ha hl hc hpay hframe he htag hprefix hreturn
theorem fromMetadata (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged size : OTerm alpha)
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
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 have hchildren := VisitListCompletionProof.actualFiniteVisits R body alpha Delta size jobs tagged hsize htag hall
 apply VisitListCompletionSyntax.completionCases R size tagged _ hchildren
 intro beta j Theta count produced hi hcp
 rw [JobCompletionSyntax.completionRename]
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 have hpay' := renameInto hpay j Theta hi
 have hframe' := renameInto hframe j Theta hi
 have he' := renameInto he j Theta hi
 have htag' := renameInto htag j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have hsize' := renameInto hsize j Theta hi
 have hall' := renameInto hall j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,admissibleRename] at hj' ht' hr' hp' ha' hl' hc' hpay' hframe' he' htag' hadm' hsize' hall'
 exact fromChildren R H M W (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (returnFrame.relabel j) (jobs.relabel j) (tagged.relabel j) count produced (size.relabel j)
   hj' ht' hr' hp' ha' hl' hc' hpay' hframe' he' htag' (andRight hcp) hadm' hsize' (andLeft hcp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedLocalCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedLocalCore
