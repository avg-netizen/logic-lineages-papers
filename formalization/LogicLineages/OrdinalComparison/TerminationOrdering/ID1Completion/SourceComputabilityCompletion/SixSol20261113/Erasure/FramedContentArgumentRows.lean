module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProducedLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentRows
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open InternalTagArithmeticSyntaxProof (suc)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime FramedContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fromRows (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged forward produced size count value : OTerm alpha)
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
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (contentProgram R)) forward jobs)))
 (hrev : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs))) :
 Nonempty (Derivation body Delta (Content R job value)) := by
 have hcounted := ContentVisitsProof.actualMappedVisits R body alpha Delta size jobs tagged forward produced
   hsize htag hall hcontent hm hrev
 have hcompletion := VisitListCompletionProof.actualFiniteVisits R body alpha Delta size jobs tagged hsize htag hall
 have hlen := FramedContentProducedLengthProof.actualLength R size tagged produced hcompletion hcounted
 have hlength := SourceFramedExpansionLengthProof.actualLength job (numeral 1) (numeral 0) typed rawJob raw parameter gamma c
   children deletions jobs hj ht hr hp ha hl he
 have hsizeeq := valueUnique OriginalContextInsertion.length size (add children deletions)
   (Fin.cons jobs Fin.elim0) hsize hlength
 have hproduced := outputTransport OriginalContextInsertion.length size (add children deletions)
   (Fin.cons produced Fin.elim0) hsizeeq hlen
 apply ContentVisitsSyntax.countedCases R tagged produced _ hcounted
 intro beta j Theta prefixCount hinc hprefix
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
 have hm' := renameInto hm j Theta hinc
 have hrev' := renameInto hrev j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hproduced' := renameInto hproduced j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,admissibleRename,
   OriginalContextInsertionSyntaxProof.lengthRename,JobFrameSyntax.frameRename,
   InternalOriginalOrderSyntaxProof.addRelabel] at hj' ht' hr' hp' hadm' ha' hl' hc' hpay' hframe' he' htag' hm' hrev' hf' hproduced'
 simp only [Content,graph1Rename]
 exact FramedContentArgumentCore.fromPrefix R H M W
   (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (returnFrame.relabel j) (jobs.relabel j) (tagged.relabel j) (forward.relabel j) (produced.relabel j) prefixCount (count.relabel j) (value.relabel j)
   hj' ht' hr' hp' hadm' ha' hl' hc' hpay' hframe' he' htag' hm' hrev' hprefix hf' hproduced'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentRows
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentRows
