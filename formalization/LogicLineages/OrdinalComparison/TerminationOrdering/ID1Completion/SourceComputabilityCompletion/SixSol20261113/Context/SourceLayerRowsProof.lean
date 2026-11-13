module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProducedLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalAdditionLawsProof (add)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Runtime SixSol20261113.Erasure
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem fromRows (R : Program 2) (H : Program 1) (M W : Program 2)
 (packed typ raw parameter c gamma job typed rawJob B children deletions counts payload frame jobs tagged forward produced out size : OTerm alpha)
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (haccept : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)))
 (hadm : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W z typ raw gamma c)))
 (hjob : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hjobGraph : Nonempty (Derivation body Delta (graph2 OriginalHereditaryEvaluatorDefinitions.job job packed parameter)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)))
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob (OriginalHereditaryEvaluatorDefinitions.evaluator R))) forward jobs)))
 (hrev : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward)))
 (hsize : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)))
 (hall : Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)))
 (hcontent : Nonempty (Derivation body Delta (ContentVisitsDefinitions.AllContent R size jobs)))
 : Nonempty (Derivation body Delta ((graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out packed parameter).iff (graph2 (OriginalHereditaryObservationLayer.layer R (OriginalHereditaryEvaluatorDefinitions.evaluator R)) out packed parameter))) := by
 have hcounted := ContentVisitsProof.actualMappedVisits R body alpha Delta size jobs tagged forward produced hsize htag hall hcontent hm hrev
 have hcompletion := VisitListCompletionProof.actualFiniteVisits R body alpha Delta size jobs tagged hsize htag hall
 have hlen := FramedContentProducedLengthProof.actualLength R size tagged produced hcompletion hcounted
 have hlength := SourceFramedExpansionLengthProof.actualLength job z typ typed rawJob raw parameter gamma c children deletions jobs hj ht hr hp ha hl he
 have heq := valueUnique OriginalContextInsertion.length size (add children deletions) (Fin.cons jobs Fin.elim0) hsize hlength
 have hproduced := outputTransport OriginalContextInsertion.length size (add children deletions) (Fin.cons produced Fin.elim0) heq hlen
 apply ContentVisitsSyntax.countedCases R tagged produced _ hcounted
 intro beta j Theta prefixCount hi hprefix
 have hpacked' := renameInto hpacked j Theta hi
 have hp' := renameInto hp j Theta hi
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have haccept' := renameInto haccept j Theta hi
 have hadm' := renameInto hadm j Theta hi
 have hjob' := renameInto hjob j Theta hi
 have hjobGraph' := renameInto hjobGraph j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 have hpay' := renameInto hpay j Theta hi
 have hframe' := renameInto hframe j Theta hi
 have he' := renameInto he j Theta hi
 have htag' := renameInto htag j Theta hi
 have hm' := renameInto hm j Theta hi
 have hrev' := renameInto hrev j Theta hi
 have hproduced' := renameInto hproduced j Theta hi
 simp only [graph1Rename,graph2Rename,zRelabel,numeralRename,termAcceptedRename,admissibleRename,OriginalHereditaryInternalAgendaSyntaxProof.jobRename,OriginalContextInsertionSyntaxProof.lengthRename,PrefixFrameSyntax.frameRename,InternalOriginalOrderSyntaxProof.addRelabel] at hpacked' hp' hj' ht' hr' haccept' hadm' hjob' hjobGraph' ha' hl' hc' hpay' hframe' he' htag' hm' hrev' hproduced'
 simp only [OriginalTypedDecoderTransportLogicalProof.iffRename,graph2Rename]
 exact SourceLayerReturnProof.fromPrefix R H M W
   (packed.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (job.relabel j) (typed.relabel j) (rawJob.relabel j) (B.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (jobs.relabel j) (tagged.relabel j) (forward.relabel j) (produced.relabel j) (out.relabel j) prefixCount
   hpacked' hp' hj' ht' hr' haccept' hadm' hjob' hjobGraph' ha' hl' hc' hpay' hframe' he' htag' hm' hrev' hprefix hproduced'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SourceLayerRowsProof
