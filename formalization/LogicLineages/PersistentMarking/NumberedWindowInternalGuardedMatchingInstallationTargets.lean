module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMeasuredInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedPathTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchedPathTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchingInstallationTargets
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

open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure CombineCalibrated)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalFactoredCoverTargets (factoredCover TermMeasureCalibrated GrammarOptionCalibrated)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredFactoredExchange)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseApplicationHopTargets (premises provided)

open NumberedWindowInternalSparseMeasuredInstallationTargets (FunctionApplicationAt SingletonAt)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated intrinsicQuery windowUpdate)
open NumberedWindowInternalSparseMatchedPathTargets (MatchedPathAt)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)

open NumberedWindowInternalSparseIntrinsicInstallationTargets (AuxWindowAt)
open NumberedWindowInternalOwnCoverReportsTargets (syntaxFlag)
open NumberedWindowInternalGuardedMatchedPathTargets (GuardedPathAt)

def GuardedAt (baseV baseM : Program 1) (P : Program 2) (G : Program 3) : Prop :=
  let V := syntaxFlag baseV
  let M := selectedMeasure (measureUpdate baseM P)
  let C := factoredCover V M G
  ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
    ∃ (i j cv tv : Program 1) (base : Program 2) (intrinsicBase : Program 2) (T : Program 1) (d oldCore oldLeast root other : Program 3) (v : Inputs),
      ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
      ActualTermExchange s base ∧ IntrinsicWindowCalibrated s intrinsicBase ∧ TypeGuardCalibrated s T ∧
      let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate intrinsicBase T))
      ActualPackedWindow s baseW ∧ AuxWindowAt baseW T ∧
      let Wp := window C s baseW V
      let X := measuredFactoredExchange s base V baseM P G
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
      EdgeMinimumEqualityAt C X Wp s ∧ SameLeastOnEdge C X Wp s ∧ FunctionApplicationAt C s X Wp ∧ SingletonAt C s X Wp raw ∧ GuardedPathAt C s X Wp T raw

def ExactGuardedMatchingInstallation : Prop :=
  ∃ (baseV baseM : Program 1) (P : Program 2) (G : Program 3),
    let V := syntaxFlag baseV
    ActualRawSyntax V ∧ TermMeasureCalibrated baseM ∧ CombineCalibrated P ∧ GrammarOptionCalibrated G ∧
    ActualSelectedCoverOutput (factoredCover V (selectedMeasure (measureUpdate baseM P)) G) ∧ GuardedAt baseV baseM P G

end LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchingInstallationTargets
