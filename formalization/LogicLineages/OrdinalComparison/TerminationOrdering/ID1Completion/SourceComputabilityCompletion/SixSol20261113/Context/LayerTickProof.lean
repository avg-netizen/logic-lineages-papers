module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionReturnContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LayerTickProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
theorem atFields (R Q : Program 2) (H : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (packed typ raw parameter c gamma job typed rawJob childCount deletionCount counts payload frame rawJobs annotatedPrefix childRow backwardChildren deletionPrefix produced old input work results suffix output outWork stack value outOld root tail returned deletionRow : OTerm alpha)
    (deletionJobs inheritedJobs deletionForward remainder : OTerm alpha)
    (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
    (hparameter : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
    (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)))
    (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) childCount raw)))
    (hgamma : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletionCount gamma)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts childCount deletionCount)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
    (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)))
    (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix childCount z typ raw rawJobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) childRow annotatedPrefix)))
    (hrev : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse backwardChildren childRow)))
    (hd : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletionCount deletionPrefix)))
    (hproduced : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced deletionPrefix backwardChildren)))
    (hresults : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
    (hinput : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
    (hwork : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame suffix)))
    (hrun : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc z) input)))
    (hout : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output outWork stack)))
    (hstack : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack value outOld)))
    (hvalue : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)))
    (htail : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail returned deletionRow)))
    (hjobs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs deletionJobs raw parameter)))
    (hinherited : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) SixSol20261112.Context.InheritedMapDefinitions.inheritedJob) inheritedJobs deletionJobs typ)))
    (hmapDeletion : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) deletionForward inheritedJobs)))
    (hreverseDeletion : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse deletionPrefix deletionForward)))
    (hpartition : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results deletionPrefix remainder))) :
    Nonempty (Derivation body Delta (graph2 (OriginalHereditaryObservationLayer.layer R Q) value packed parameter)) := by
  have hcontent := TermTickContentProof.actual R Q H M W body alpha Delta
    packed typ raw parameter c gamma job typed rawJob childCount deletionCount counts payload frame rawJobs annotatedPrefix childRow backwardChildren deletionPrefix produced old input work results suffix output outWork stack value outOld root tail returned deletionRow
    hpacked hparameter hj ht hr ha harity hgamma hc hp hframe he hscan hm hrev hd hproduced hresults hinput hwork hrun hout hstack hvalue htail
  have hcoords := OriginalReturnFrameCoordinatesProof.actualCoordinates body alpha Delta input work results
    frame suffix (numeral 1) payload job counts z typed rawJob typ raw parameter childCount deletionCount packed
    hinput hframe hp hj ht hr hc hpacked hwork
  have hchildren := InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft hcoords)))
  have hdeletions := InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft hcoords))
  have hres := InternalApplicationStepPeelSupportProof.andRight hcoords
  have hselected := InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hcontent))
  have hscalar := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalHereditaryResultStackProgram.deletionRow
    OriginalHereditaryReturnStep.childCount OriginalHereditaryReturnStep.deletionCount OriginalHereditaryReturnStep.results
    deletionRow childCount deletionCount results (Fin.cons input Fin.elim0) hselected hchildren hdeletions hres
  have hrows := DeletionReturnContentProof.actual Q body alpha Delta packed typ raw parameter deletionJobs inheritedJobs
    deletionForward deletionPrefix childCount deletionCount remainder results deletionRow hpacked hjobs hinherited
    hmapDeletion hreverseDeletion hd hpartition hscalar
  exact OriginalHereditaryObservationLayerInternalProof.assembly R Q packed parameter value tail root returned deletionRow
    hvalue htail (InternalApplicationStepPeelSupportProof.andLeft hcontent)
    (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hcontent)) hrows
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LayerTickProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LayerTickProof
