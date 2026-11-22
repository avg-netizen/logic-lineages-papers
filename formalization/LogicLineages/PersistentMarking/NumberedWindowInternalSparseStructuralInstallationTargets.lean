module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralInstallationTargets
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

open NumberedWindowInternalSparseCoveredWindowTargets (WindowSeedsCovered coveredWindow)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)

open NumberedWindowInternalSparseCanonicalAddressTargets (addressScalar)
open NumberedWindowInternalSparseCoveredInstallationTargets (SameLeastOnEdge)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalPresentationTargets (data)
open ID1Completion.InternalAccessibilityRules (edge carrier)

open NumberedWindowInternalSparseScalarInstallationTargets (EdgeCarriersAt)
open NumberedWindowInternalSparseStructuralApplicationTargets (window exchange FunctionEdgeAt)

/-- The cover and term-syntax callbacks can be physically selected before the
settings. The positive and application checkers share the same lifted exchange
and window through the literal least program, on one reinstalled tuple. -/
def At (C : Program 3) (V : Program 1) : Prop :=
  ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
    ∃ (i j cv tv : Program 1) (base : Program 2) (d oldCore oldLeast root other baseW : Program 3) (v : Inputs),
      ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
      ActualTermExchange s base ∧ ActualPackedWindow s baseW ∧
      let Wp := window C s baseW V
      let X := exchange C s base V
      let raw := typedRaw5 root other Wp V
      let least := packedLeastProgram C X Wp s
      let newI := addressScalar cv tv Wp least
      let final := frontendInputs newI least v
      ActualTermExchange s X ∧ ActualPackedWindow s Wp ∧ ActualLeastCalibration s least ∧
      ActualScalarCalibration s newI ∧
      InstalledTupleAt entries s W i j cv tv d oldCore raw oldLeast v ∧
      InstalledTupleAt entries s W i j cv tv d oldCore raw least v ∧ chosenA final = chosenA v ∧
      InstalledTupleAt entries s W newI j cv tv d (applicationCore least) raw least final ∧
      EdgeCarriersAt newI j (addressPositive cv tv raw least) d ∧
      OpenCoverAt C X Wp s ∧ MinimumEdgeAt C X Wp s ∧ PositiveEndpointsAt raw least Wp ∧
      EdgeCoverAt C X Wp s ∧ EdgeMinimumOrderAt C X Wp s ∧ MutualEdgeMinimumEqualityAt C X Wp s ∧
      EdgeMinimumEqualityAt C X Wp s ∧ SameLeastOnEdge C X Wp s ∧ FunctionEdgeAt C s X Wp

def ExactInstallAt : Prop := ∀ (C : Program 3) (V : Program 1),
  ActualSelectedCoverOutput C → ActualRawSyntax V → At C V

def ExactStructuralInstallation : Prop := ∃ (C : Program 3) (V : Program 1),
  ActualSelectedCoverOutput C ∧ ActualRawSyntax V ∧ At C V

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralInstallationTargets
