module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.LayerTickProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReturnTickQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformLayerAtGeometryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
theorem actual (R Q : Program 2) (H : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (packed typ raw parameter c gamma job typed rawJob childCount deletionCount counts payload frame rawJobs annotatedPrefix childRow backwardChildren deletionPrefix produced value : OTerm alpha)
    (deletionJobs inheritedJobs deletionForward : OTerm alpha)
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
    (hjobs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs deletionJobs raw parameter)))
    (hinherited : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) SixSol20261112.Context.InheritedMapDefinitions.inheritedJob) inheritedJobs deletionJobs typ)))
    (hmapDeletion : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) deletionForward inheritedJobs)))
    (hreverseDeletion : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse deletionPrefix deletionForward)))
    (hreturn : Nonempty (Derivation body Delta (SixSol20261113.Runtime.UniformReturnDefinitions.Framed R frame produced value))) :
    Nonempty (Derivation body Delta (graph2 (OriginalHereditaryObservationLayer.layer R Q) value packed parameter)) := by
  apply ReturnTickQueries.withTick R frame produced value _ hreturn
  intro beta j Theta work input stack output root tail returned deletionRow hi hw hin ho hs hpv hpt hrun
  rw [graph2Rename]
  have hpacked' := renameInto hpacked j Theta hi
  have hparameter' := renameInto hparameter j Theta hi
  have hj' := renameInto hj j Theta hi
  have ht' := renameInto ht j Theta hi
  have hr' := renameInto hr j Theta hi
  have ha' := renameInto ha j Theta hi
  have harity' := renameInto harity j Theta hi
  have hgamma' := renameInto hgamma j Theta hi
  have hc' := renameInto hc j Theta hi
  have hp' := renameInto hp j Theta hi
  have hframe' := renameInto hframe j Theta hi
  have he' := renameInto he j Theta hi
  have hscan' := renameInto hscan j Theta hi
  have hm' := renameInto hm j Theta hi
  have hrev' := renameInto hrev j Theta hi
  have hd' := renameInto hd j Theta hi
  have hproduced' := renameInto hproduced j Theta hi
  have hjobs' := renameInto hjobs j Theta hi
  have hinherited' := renameInto hinherited j Theta hi
  have hmapDeletion' := renameInto hmapDeletion j Theta hi
  have hreverseDeletion' := renameInto hreverseDeletion j Theta hi
  simp only [graph1Rename,graph2Rename,graph5Rename,OriginalContextInsertion.lengthGraph,termAcceptedRename,zRelabel,numeralRename] at hpacked' hparameter' hj' ht' hr' ha' harity' hgamma' hc' hp' hframe' he' hscan' hm' hrev' hd' hproduced' hjobs' hinherited' hmapDeletion' hreverseDeletion'
  have hzero := SixSol20261112.Context.AppendIdentityProof.actualRightZero body beta Theta (produced.relabel j)
  exact LayerTickProof.atFields R Q H M W body beta Theta
    (packed.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (job.relabel j) (typed.relabel j) (rawJob.relabel j) (childCount.relabel j) (deletionCount.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (rawJobs.relabel j) (annotatedPrefix.relabel j) (childRow.relabel j) (backwardChildren.relabel j) (deletionPrefix.relabel j) (produced.relabel j)
    z input work (produced.relabel j) z output z stack (value.relabel j) z root tail returned deletionRow
    (deletionJobs.relabel j) (inheritedJobs.relabel j) (deletionForward.relabel j) (backwardChildren.relabel j)
    hpacked' hparameter' hj' ht' hr' ha' harity' hgamma' hc' hp' hframe' he' hscan' hm' hrev' hd' hproduced' hzero hin hw hrun ho hs hpv hpt
    hjobs' hinherited' hmapDeletion' hreverseDeletion' hproduced'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformLayerAtGeometryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UniformLayerAtGeometryProof
