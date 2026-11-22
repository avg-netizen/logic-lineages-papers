module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedRounds (poolLength)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparseScalarEdge (edgeGraph)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalCoverCombinedRestrictedCrossCoverTargets (CrossCoverReports)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

/-- A successor output of the original physical length program on exactly
the same standard scratch tape, not a decoded or reordered substitute. -/
def PositiveLengthK {α : Type} (body : Positive (Fin 1)) (Γ : List (Formula α))
    (vertices : OTerm α) (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (fuel : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    Nonempty (Derivation body Δ (unary poolLength (suc fuel) (vertices.relabel j))) →
    Nonempty (Derivation body Δ (goal.relabel j))

def ExactOpenCoverPositiveScratchLength : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices k : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (memberGraph vertices k)) →
    PositiveLengthK body Γ vertices goal →
    Nonempty (Derivation body Γ goal)

/-- No separate successor-length premise for the literal paired seeds. -/
def ExactOpenCoverCombinedRestrictedPairedReach : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f g arg vertices pool : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let X := guardedExchange P.cover s (thinPairedExchange (directedX base P.V))
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    CrossCoverReports P.cover s body Γ a b vertices →
    Nonempty (Derivation body Γ (edgeGraph X W ctx cod a b)) →
    Nonempty (Derivation body Γ (programGraph (membersAtSeed P.cover X W s) pool ![ctx,cod,a])) →
    Nonempty (Derivation body Γ (memberGraph pool b))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPositiveLengthTargets
