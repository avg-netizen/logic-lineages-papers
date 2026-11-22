module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationTargets
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

def EdgeCarriersAt (i j : Program 1) (r d : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (c : Nat) (α : Type) (Γ : List (Formula α)) (a b : OTerm α),
    let S := data i j r d
    Nonempty (Derivation body Γ ((edge S false c a b).imp (carrier S false c a ⊓ carrier S false c b)))

/-- Rebuild the original body and guarded application at a new genuinely
calibrated scalar, including the fresh formulas depending on that body. -/
def ExactReinstallScalar : Prop :=
  ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i oldI j cv tv : Program 1) (d oldCore : Program 3) (raw : Program 5) (least : Program 3) (v : Inputs),
      ActualScalarCalibration s i → InstalledTupleAt entries s W oldI j cv tv d oldCore raw least v →
      let updated := frontendInputs i least v
      chosenA updated = chosenA v ∧ InstalledTupleAt entries s W i j cv tv d (applicationCore least) raw least updated

def ExactPhysicalEdgeCarriers : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (baseW root other : Program 3)
    (syntaxProg cv tv j : Program 1) (d : Program 3),
    let windowProg := coveredWindow C s baseW
    let X := guardedExchange C s (pairedExchange baseX)
    let least := packedLeastProgram C X windowProg s
    let raw := typedRaw5 root other windowProg syntaxProg
    EdgeCarriersAt (addressScalar cv tv windowProg least) j (addressPositive cv tv raw least) d

/-- The same chosen exchange and window programs are used at all open inputs,
including by the least program installed in the final application tuple. -/
def ExactScalarInstallation : Prop :=
  ∃ C : Program 3, ActualSelectedCoverOutput C ∧
    ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W → HeadPairsSymmetric s.equivalentHeads → WindowSeedsCovered s →
      ∃ (i j cv tv syntaxProg : Program 1) (baseX : Program 2)
        (d oldCore oldLeast root other baseW : Program 3) (v : Inputs),
        ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧
        ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s baseW ∧
        let windowProg := coveredWindow C s baseW
        ActualPackedWindow s windowProg ∧
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
        EdgeMinimumEqualityAt C X windowProg s ∧ SameLeastOnEdge C X windowProg s ∧
        let newI := addressScalar cv tv windowProg least
        let selected := frontendInputs newI least v
        ActualScalarCalibration s newI ∧ chosenA selected = chosenA v ∧
        InstalledTupleAt entries s W newI j cv tv d (applicationCore least) raw least selected ∧
        EdgeCarriersAt newI j (addressPositive cv tv raw least) d

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationTargets
