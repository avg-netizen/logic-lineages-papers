module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumTargets
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

/-- A directed edge from a to b and successful calls at both seeds imply
minimum(a) ≤ minimum(b). No cover, pool, length, or seed-membership input. -/
def EdgeMinimumOrderAt (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b x y : OTerm α),
    let minima := leastGraph C X W s ctx ty a x ⊓ leastGraph C X W s ctx ty b y
    Nonempty (Derivation body Γ ((minima ⊓ acceptEdge (edge4 X W) ctx ty a b).imp (strictLess y x).not))

def MutualEdgeMinimumEqualityAt (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b x y : OTerm α),
    let minima := leastGraph C X W s ctx ty a x ⊓ leastGraph C X W s ctx ty b y
    let edges := acceptEdge (edge4 X W) ctx ty a b ⊓ acceptEdge (edge4 X W) ctx ty b a
    Nonempty (Derivation body Γ ((minima ⊓ edges).imp (eqn x y)))

def ExactEdgeMinimumOrder : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3),
    EdgeMinimumOrderAt C (guardedExchange C s baseX) W s

def ExactMutualEdgeMinimumEquality : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3),
    MutualEdgeMinimumEqualityAt C (guardedExchange C s baseX) W s

/-- The same chosen exchange and window programs are used at all open inputs,
including by the least program installed in the final application tuple. -/
def ExactAdjacentInstallation : Prop :=
  ∃ C : Program 3, ActualSelectedCoverOutput C ∧
    ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
      ∃ (i j cv tv syntaxProg : Program 1) (baseX : Program 2)
        (d oldCore oldLeast root other windowProg : Program 3) (v : Inputs),
        ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧
        ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
        ActualTermExchange s baseX ∧
        let X := guardedExchange C s baseX
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
        EdgeMinimumOrderAt C X windowProg s ∧ MutualEdgeMinimumEqualityAt C X windowProg s

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumTargets
