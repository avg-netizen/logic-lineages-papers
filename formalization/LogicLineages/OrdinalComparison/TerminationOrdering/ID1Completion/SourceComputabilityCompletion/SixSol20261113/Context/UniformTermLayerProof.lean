module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformTermLayerSuffixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformTermLayerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Runtime
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem actual (R Q : Program 2) (H : Program 1) (M W : Program 2)
    (packed typ raw parameter c gamma job typed rawJob children deletions counts payload frame jobs forward produced value : OTerm alpha)
    (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
    (haccept : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)))
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
    (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
    (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
    (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) forward jobs)))
    (hrev : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward)))
    (hreturn : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)))
    : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryObservationLayer.layer R Q) value packed parameter)) := by
  apply ExpansionMapGeometryProof.partitionStrong (ChildContentDefinitions.observationFromJob Q)
    job z typ typed rawJob raw parameter c gamma children deletions jobs forward produced _ hj ht hr hp ha hl he hm hrev
  intro beta j Theta rawJobs annotatedPrefix childRow backwardChildren deletionPrefix annotatedSuffix suffixForward hi hg happ hmapSuffix hrevSuffix
  rw [graph2Rename]
  have hpacked' := renameInto hpacked j Theta hi
  have hp' := renameInto hp j Theta hi
  have hj' := renameInto hj j Theta hi
  have ht' := renameInto ht j Theta hi
  have hr' := renameInto hr j Theta hi
  have haccept' := renameInto haccept j Theta hi
  have ha' := renameInto ha j Theta hi
  have hl' := renameInto hl j Theta hi
  have hc' := renameInto hc j Theta hi
  have hpay' := renameInto hpay j Theta hi
  have hframe' := renameInto hframe j Theta hi
  have he' := renameInto he j Theta hi
  have hm' := renameInto hm j Theta hi
  have hrev' := renameInto hrev j Theta hi
  have hreturn' := renameInto hreturn j Theta hi
  simp only [graph1Rename,graph2Rename,graph5Rename,OriginalContextInsertion.lengthGraph,termAcceptedRename,zRelabel,numeralRename,UniformReturnSyntax.frameRename,ExpansionMapGeometryDefinitions.Geometry,InternalRecursionGraphStepSyntaxProof.conjunctionRename] at hpacked' hp' hj' ht' hr' haccept' ha' hl' hc' hpay' hframe' he' hm' hrev' hreturn'
  simp only [zRelabel] at hg
  exact UniformTermLayerSuffixProof.atPartition R Q H M W
    (packed.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (job.relabel j) (typed.relabel j) (rawJob.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (jobs.relabel j) (forward.relabel j) (produced.relabel j) (value.relabel j)
    rawJobs annotatedPrefix childRow backwardChildren deletionPrefix annotatedSuffix suffixForward
    hpacked' hp' hj' ht' hr' haccept' ha' hl' hc' hpay' hframe' he' hm' hrev' hreturn' hg happ hmapSuffix hrevSuffix
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformTermLayerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformTermLayerProof
