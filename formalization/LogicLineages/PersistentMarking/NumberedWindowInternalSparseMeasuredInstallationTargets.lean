module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMeasuredInstallationTargets
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

def FunctionApplicationAt (C : Program 3) (s : Settings) (X : Program 2) (Wp : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod f g arg value : OTerm α),
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    let E := edge4 X Wp
    let input := acceptEdge E ctx (rawCons dom cod) f g ⊓ (windowAt Wp ctx cod a ⊓ windowAt Wp ctx cod b)
    Nonempty (Derivation body Γ (input.imp (acceptEdge E ctx cod a b ⊓
      ((leastGraph C X Wp s ctx cod a value).imp (leastGraph C X Wp s ctx cod b value)))))

def SingletonAt (C : Program 3) (s : Settings) (X : Program 2) (Wp : Program 3) (raw : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod arg f child g : OTerm α),
    Nonempty (Derivation body Γ ((premises raw Wp ctx dom cod arg f child g).imp
      (provided C X Wp s raw ctx cod (auxiliaryTerm dom cod f arg) (functionWitnessTerm child)
        (auxiliaryTerm dom cod g arg))))

def At (V baseM : Program 1) (P : Program 2) (G : Program 3) : Prop :=
  let M := selectedMeasure (measureUpdate baseM P)
  let C := factoredCover V M G
  ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
    ∃ (i j cv tv : Program 1) (base : Program 2) (d oldCore oldLeast root other baseW : Program 3) (v : Inputs),
      ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧ ActualFallback other ∧
      ActualTermExchange s base ∧ ActualPackedWindow s baseW ∧
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
      EdgeMinimumEqualityAt C X Wp s ∧ SameLeastOnEdge C X Wp s ∧ FunctionApplicationAt C s X Wp ∧ SingletonAt C s X Wp raw

def ExactMeasuredInstallation : Prop :=
  ∃ (V baseM : Program 1) (P : Program 2) (G : Program 3),
    ActualRawSyntax V ∧ TermMeasureCalibrated baseM ∧ CombineCalibrated P ∧ GrammarOptionCalibrated G ∧
    ActualSelectedCoverOutput (factoredCover V (selectedMeasure (measureUpdate baseM P)) G) ∧ At V baseM P G

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMeasuredInstallationTargets
