module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentProducedLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentCore
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
theorem fromReturn (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged forward produced prefixCount count value canonicalValue : OTerm alpha)
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
 (hprefix : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged prefixCount produced)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (hreturn : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R returnFrame produced canonicalValue))) :
 Nonempty (Derivation body Delta (Content R job value)) := by
 have hcontent := ArgumentReturnContentProof.actualArgumentReturnContent R
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) H M W body alpha Delta
   job typed rawJob raw parameter gamma c children deletions counts payload returnFrame jobs forward produced canonicalValue
   hj ht hr hp hadm ha hl hc hpay hframe he hm hrev hreturn
 have hcanonical := SourceFramedRunProof.framed R job (numeral 1) typed (numeral 0) rawJob raw parameter c gamma
   children deletions counts payload returnFrame jobs tagged prefixCount produced canonicalValue
   hj ht hr hp ha hl hc hpay hframe he htag hprefix hreturn
 exact FramedContentTransferProof.fromCanonical R job count value
   (suc (add prefixCount (suc (numeral 0)))) canonicalValue hcanonical hcontent hf
theorem fromPrefix (R : Program 2) (H : Program 1) (M W : Program 2)
 (job typed rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged forward produced prefixCount count value : OTerm alpha)
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
 (hprefix : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged prefixCount produced)))
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add children deletions) produced))) :
 Nonempty (Derivation body Delta (Content R job value)) := by
 have hreturn := UniformReturnProof.actualUniformReturn R H M W body alpha Delta
   job (numeral 1) (numeral 0) typed rawJob raw parameter gamma c children deletions counts payload returnFrame produced
   hj ht hr hp hadm ha hl hc hpay hframe hlen
 apply UniformReturnCompletionSyntax.completionCases R returnFrame produced _ hreturn
 intro beta j Theta canonicalValue hinc hret
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
 have hprefix' := renameInto hprefix j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [graph1Rename,graph2Rename,numeralRename,admissibleRename,
   OriginalContextInsertionSyntaxProof.lengthRename,PrefixFrameSyntax.frameRename,JobFrameSyntax.frameRename]
   at hj' ht' hr' hp' hadm' ha' hl' hc' hpay' hframe' he' htag' hm' hrev' hprefix' hf'
 simp only [Content,graph1Rename]
 exact fromReturn R H M W (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (returnFrame.relabel j) (jobs.relabel j) (tagged.relabel j) (forward.relabel j) (produced.relabel j) (prefixCount.relabel j) (count.relabel j) (value.relabel j) canonicalValue
   hj' ht' hr' hp' hadm' ha' hl' hc' hpay' hframe' he' htag' hm' hrev' hprefix' hf' hret
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentArgumentCore
