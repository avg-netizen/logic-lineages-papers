module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickMapLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTermProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedReturnContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickAtSlotsProof
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
open OriginalContextInsertionSyntaxProof (lengthGraphRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
theorem actual (R Q : Program 2) (H : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (packed typ raw parameter c gamma job typed rawJob childCount deletionCount counts payload frame rawJobs annotatedPrefix childRow backwardChildren deletionPrefix produced old input work results suffix output outWork stack value outOld root tail returned deletionRow : OTerm alpha)
    (first second : OTerm alpha)
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
    (hsecond : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) childRow))) :
  Nonempty (Derivation body Delta
    (graph2 (OriginalRootObservation.rootObservation R) root packed parameter ⊓
     (graph2 (OriginalRootObservation.rootObservation Q) returned packed parameter ⊓
      (graph1 OriginalHereditaryReturnStep.deletionRow deletionRow input ⊓
       graph1 OriginalHereditaryReturnStep.oldSuffix outOld input)))) := by
  have hlen := TermTickMapLengthProof.actual (ChildContentDefinitions.observationFromJob Q)
    childCount z typ raw rawJobs annotatedPrefix childRow first second harity hscan hm hfirst hsecond
  have hslots := ReverseChildSlotsProof.actual body alpha Delta raw childCount deletionCount
    childRow backwardChildren deletionPrefix produced old results first second harity hlen hrev hd hproduced hresults hfirst hsecond
  have hcoords := OriginalReturnFrameCoordinatesProof.actualCoordinates body alpha Delta input work results
    frame suffix (numeral 1) payload job counts z typed rawJob typ raw parameter childCount deletionCount packed
    hinput hframe hp hj ht hr hc hpacked hwork
  have hrole := InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft hcoords))))))
  have hparam := InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft hcoords))))
  have hchildren := InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft hcoords)))
  have hdeletions := InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andLeft hcoords))
  have hpack := InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andLeft hcoords)
  have hres := InternalApplicationStepPeelSupportProof.andRight hcoords
  have hfirstSlot := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.firstSlot
    input childCount deletionCount results first hchildren hdeletions hres (InternalApplicationStepPeelSupportProof.andLeft hslots)
  have hsecondSlot := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.secondSlot
    input childCount deletionCount results second hchildren hdeletions hres (InternalApplicationStepPeelSupportProof.andRight hslots)
  have hreturned := SixSol20261113.Runtime.FramedReturnContentProof.actualFramedReturnContent R body alpha Delta
    input work results frame suffix payload packed parameter first second output outWork stack value outOld root tail returned deletionRow
    hinput hwork hframe hrole hpack hparam hfirstSlot hsecondSlot hrun hout hstack hvalue htail
  have hinner := AdmittedTermProof.actual Q H M W body alpha Delta packed typ raw parameter c gamma
    childCount rawJobs annotatedPrefix childRow first second returned hpacked hparameter ha harity he hscan hm hfirst hsecond
    (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hreturned))
  exact InternalApplicationStepPeelSupportProof.andIntro (InternalApplicationStepPeelSupportProof.andLeft hreturned)
    (InternalApplicationStepPeelSupportProof.andIntro hinner
      (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hreturned)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickAtSlotsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickAtSlotsProof
