module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformLayerAtGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedSuffixQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformTermLayerSuffixProof
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
theorem atPartition (R Q : Program 2) (H : Program 1) (M W : Program 2)
    (packed typ raw parameter c gamma job typed rawJob children deletions counts payload frame jobs forward produced value rawJobs annotatedPrefix childRow backwardChildren deletionPrefix annotatedSuffix suffixForward : OTerm alpha)
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
    (hg : Nonempty (Derivation body Delta (ExpansionMapGeometryDefinitions.Geometry (ChildContentDefinitions.observationFromJob Q) z typ raw parameter children deletions produced rawJobs annotatedPrefix childRow backwardChildren deletionPrefix)))
    (happ : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs annotatedPrefix annotatedSuffix)))
    (hmapSuffix : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) suffixForward annotatedSuffix)))
    (hrevSuffix : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse deletionPrefix suffixForward)))
    : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryObservationLayer.layer R Q) value packed parameter)) := by
  have g0 := andLeft (hg)
  have g1 := andLeft (andRight (hg))
  have g2 := andLeft (andRight (andRight (hg)))
  have g3 := andLeft (andRight (andRight (andRight (hg))))
  have g4 := andLeft (andRight (andRight (andRight (andRight (hg)))))
  have g5 := andLeft (andRight (andRight (andRight (andRight (andRight (hg))))))
  have g6 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (hg)))))))
  have g7 := andRight (andRight (andRight (andRight (andRight (andRight (andRight (hg)))))))
  apply InheritedSuffixQueries.withInherited children typ raw parameter c gamma rawJob typed job rawJobs annotatedPrefix jobs annotatedSuffix _
    hp hr ht hj ha g0 g1 he happ
  intro beta j Theta deletionJobs hi hdeletion hinherited
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
  have g0' := renameInto g0 j Theta hi
  have g1' := renameInto g1 j Theta hi
  have g2' := renameInto g2 j Theta hi
  have g3' := renameInto g3 j Theta hi
  have g4' := renameInto g4 j Theta hi
  have g5' := renameInto g5 j Theta hi
  have g6' := renameInto g6 j Theta hi
  have g7' := renameInto g7 j Theta hi
  have happ' := renameInto happ j Theta hi
  have hmapSuffix' := renameInto hmapSuffix j Theta hi
  have hrevSuffix' := renameInto hrevSuffix j Theta hi
  simp only [graph1Rename,graph2Rename,graph5Rename,OriginalContextInsertion.lengthGraph,termAcceptedRename,zRelabel,numeralRename,UniformReturnSyntax.frameRename,ExpansionMapGeometryDefinitions.Geometry,InternalRecursionGraphStepSyntaxProof.conjunctionRename] at hpacked' hp' hj' ht' hr' haccept' ha' hl' hc' hpay' hframe' he' hm' hrev' hreturn' g0' g1' g2' g3' g4' g5' g6' g7' happ' hmapSuffix' hrevSuffix'
  exact UniformLayerAtGeometryProof.actual R Q H M W body beta Theta
    (packed.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (job.relabel j) (typed.relabel j) (rawJob.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (rawJobs.relabel j) (annotatedPrefix.relabel j) (childRow.relabel j) (backwardChildren.relabel j) (deletionPrefix.relabel j) (produced.relabel j) (value.relabel j)
    deletionJobs (annotatedSuffix.relabel j) (suffixForward.relabel j)
    hpacked' hp' hj' ht' hr' haccept' ha' hl' hc' hpay' hframe' g0' g1' g2' g4' g5' g6'
    hdeletion hinherited hmapSuffix' hrevSuffix' hreturn'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformTermLayerSuffixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformTermLayerSuffixProof
