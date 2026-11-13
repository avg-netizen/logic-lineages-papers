module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickAtSlotsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalContextInsertion (lengthGraph)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
theorem withFirst (R Q : Program 2) (H : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (packed typ raw parameter c gamma job typed rawJob childCount deletionCount counts payload frame rawJobs annotatedPrefix childRow backwardChildren deletionPrefix produced old input work results suffix output outWork stack value outOld root tail returned deletionRow : OTerm alpha)
    (first : OTerm alpha)
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
    (hfirst : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z childRow)))
    :
  Nonempty (Derivation body Delta
    (graph2 (OriginalRootObservation.rootObservation R) root packed parameter ⊓
     (graph2 (OriginalRootObservation.rootObservation Q) returned packed parameter ⊓
      (graph1 OriginalHereditaryReturnStep.deletionRow deletionRow input ⊓
       graph1 OriginalHereditaryReturnStep.oldSuffix outOld input)))) := by
  apply programCases InternalRawListRecursion.lookup (Fin.cons (suc z) (Fin.cons childRow Fin.elim0)) _
  intro beta j Theta second hjj hsecond
  simp only [graph2Rename,graph1Rename,conjunctionRename]
  have hpacked' := renameInto hpacked j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hpacked'
  have hparameter' := renameInto hparameter j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hparameter'
  have hj' := renameInto hj j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hj'
  have ht' := renameInto ht j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at ht'
  have hr' := renameInto hr j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hr'
  have ha' := renameInto ha j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at ha'
  have harity' := renameInto harity j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at harity'
  have hgamma' := renameInto hgamma j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hgamma'
  have hc' := renameInto hc j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hc'
  have hp' := renameInto hp j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hp'
  have hframe' := renameInto hframe j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hframe'
  have he' := renameInto he j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at he'
  have hscan' := renameInto hscan j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hscan'
  have hm' := renameInto hm j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hm'
  have hrev' := renameInto hrev j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hrev'
  have hd' := renameInto hd j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hd'
  have hproduced' := renameInto hproduced j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hproduced'
  have hresults' := renameInto hresults j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hresults'
  have hinput' := renameInto hinput j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hinput'
  have hwork' := renameInto hwork j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hwork'
  have hrun' := renameInto hrun j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hrun'
  have hout' := renameInto hout j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hout'
  have hstack' := renameInto hstack j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hstack'
  have hvalue' := renameInto hvalue j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hvalue'
  have htail' := renameInto htail j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at htail'
  have hfirst' := renameInto hfirst j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hfirst'
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hsecond
  exact TermTickAtSlotsProof.actual R Q H M W body beta Theta
    (packed.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (job.relabel j) (typed.relabel j) (rawJob.relabel j) (childCount.relabel j) (deletionCount.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (rawJobs.relabel j) (annotatedPrefix.relabel j) (childRow.relabel j) (backwardChildren.relabel j) (deletionPrefix.relabel j) (produced.relabel j) (old.relabel j) (input.relabel j) (work.relabel j) (results.relabel j) (suffix.relabel j) (output.relabel j) (outWork.relabel j) (stack.relabel j) (value.relabel j) (outOld.relabel j) (root.relabel j) (tail.relabel j) (returned.relabel j) (deletionRow.relabel j)
    (first.relabel j) second
    hpacked' hparameter' hj' ht' hr' ha' harity' hgamma' hc' hp' hframe' he' hscan' hm' hrev' hd' hproduced' hresults' hinput' hwork' hrun' hout' hstack' hvalue' htail' hfirst' hsecond

theorem actual : TermTickContentTargets.ActualTermTick := by
  intro R Q H M W body alpha Delta packed typ raw parameter c gamma job typed rawJob childCount deletionCount counts payload frame rawJobs annotatedPrefix childRow backwardChildren deletionPrefix produced old input work results suffix output outWork stack value outOld root tail returned deletionRow
    hpacked hparameter hj ht hr ha harity hgamma hc hp hframe he hscan hm hrev hd hproduced hresults hinput hwork hrun hout hstack hvalue htail
  apply programCases InternalRawListRecursion.lookup (Fin.cons z (Fin.cons childRow Fin.elim0)) _
  intro beta j Theta first hjj hfirst
  simp only [graph2Rename,graph1Rename,conjunctionRename]
  have hpacked' := renameInto hpacked j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hpacked'
  have hparameter' := renameInto hparameter j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hparameter'
  have hj' := renameInto hj j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hj'
  have ht' := renameInto ht j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at ht'
  have hr' := renameInto hr j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hr'
  have ha' := renameInto ha j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at ha'
  have harity' := renameInto harity j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at harity'
  have hgamma' := renameInto hgamma j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hgamma'
  have hc' := renameInto hc j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hc'
  have hp' := renameInto hp j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hp'
  have hframe' := renameInto hframe j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hframe'
  have he' := renameInto he j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at he'
  have hscan' := renameInto hscan j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hscan'
  have hm' := renameInto hm j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hm'
  have hrev' := renameInto hrev j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hrev'
  have hd' := renameInto hd j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hd'
  have hproduced' := renameInto hproduced j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hproduced'
  have hresults' := renameInto hresults j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hresults'
  have hinput' := renameInto hinput j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hinput'
  have hwork' := renameInto hwork j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hwork'
  have hrun' := renameInto hrun j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hrun'
  have hout' := renameInto hout j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hout'
  have hstack' := renameInto hstack j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hstack'
  have hvalue' := renameInto hvalue j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at hvalue'
  have htail' := renameInto htail j Theta hjj
  simp only [graph2Rename,graph1Rename,graph5Rename,OriginalContextInsertion.lengthGraph,graph1Rename,termAcceptedRename,zRelabel,sucRelabel,numeralRename] at htail'
  simp only [consTermRename,emptyRename,zRelabel] at hfirst
  exact withFirst R Q H M W body beta Theta
    (packed.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (job.relabel j) (typed.relabel j) (rawJob.relabel j) (childCount.relabel j) (deletionCount.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (rawJobs.relabel j) (annotatedPrefix.relabel j) (childRow.relabel j) (backwardChildren.relabel j) (deletionPrefix.relabel j) (produced.relabel j) (old.relabel j) (input.relabel j) (work.relabel j) (results.relabel j) (suffix.relabel j) (output.relabel j) (outWork.relabel j) (stack.relabel j) (value.relabel j) (outOld.relabel j) (root.relabel j) (tail.relabel j) (returned.relabel j) (deletionRow.relabel j)
    first
    hpacked' hparameter' hj' ht' hr' ha' harity' hgamma' hc' hp' hframe' he' hscan' hm' hrev' hd' hproduced' hresults' hinput' hwork' hrun' hout' hstack' hvalue' htail' hfirst
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickContentProof
