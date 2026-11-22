module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricExchangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricInstallationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)

open ID1Completion.InternalControlGraph (programGraph)
open ID1Completion.InternalLessThan (strictLess)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFuelBudgetTargets (runsAt)
open NumberedWindowInternalSparseDirectedRounds (poolLength members membersTape)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparseInstalledOccurrenceTargets (OpenCoverAt)

open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDirectedInstallationTargets (MinimumEdgeAt PositiveEndpointsAt)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)

open NumberedWindowInternalSparseCoverInstallationTargets (EdgeCoverAt)

open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange EdgeMinimumEqualityAt)
open NumberedWindowInternalSparseAdjacentMinimumTargets (EdgeMinimumOrderAt MutualEdgeMinimumEqualityAt)

def ExactPairedCalibration : Prop :=
  ∀ (s : Settings) (baseX : Program 2), HeadPairsSymmetric s.equivalentHeads →
    ActualTermExchange s baseX → ActualTermExchange s (pairedExchange baseX)

/-- The same chosen exchange and window programs are used at all open inputs,
including by the least program installed in the final application tuple. -/
def ExactSymmetricInstallation : Prop :=
  ∃ C : Program 3, ActualSelectedCoverOutput C ∧
    ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W → HeadPairsSymmetric s.equivalentHeads →
      ∃ (i j cv tv syntaxProg : Program 1) (baseX : Program 2)
        (d oldCore oldLeast root other windowProg : Program 3) (v : Inputs),
        ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧
        ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
        ActualTermExchange s baseX ∧
        let X := guardedExchange C s (pairedExchange baseX)
        ActualTermExchange s X ∧
        let raw := typedRaw5 root other windowProg syntaxProg
        let least := packedLeastProgram C X windowProg s
        let updated := frontendInputs i least v
        ActualLeastCalibration s least ∧
        InstalledTupleAt entries s W i j cv tv d oldCore raw oldLeast v ∧
        InstalledTupleAt entries s W i j cv tv d oldCore raw least v ∧
        chosenA updated = chosenA v ∧
        InstalledTupleAt entries s W i j cv tv d (applicationCore least) raw least updated ∧
        OpenCoverAt C X windowProg s ∧ MinimumEdgeAt C X windowProg s ∧
        PositiveEndpointsAt raw least windowProg ∧ EdgeCoverAt C X windowProg s ∧
        EdgeMinimumOrderAt C X windowProg s ∧ MutualEdgeMinimumEqualityAt C X windowProg s ∧
        EdgeMinimumEqualityAt C X windowProg s

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricInstallationTargets
