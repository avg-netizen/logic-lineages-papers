module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricExchangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)

/-- The target seed occurs in the genuine original cover at that seed.
The target least and its context parser are both recovered internally. -/
def SingleEdgeTransportAt (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b x : OTerm α),
    let source := leastGraph C X W s ctx ty a x
    let edge := acceptEdge (edge4 X W) ctx ty a b
    Nonempty (Derivation body Γ ((source ⊓ (edge ⊓ occursInCover C s b b)).imp
      (leastGraph C X W s ctx ty b x)))

def ExactPairedEdgeTransport : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3),
    SingleEdgeTransportAt C (guardedExchange C s (pairedExchange baseX)) W s
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportTargets
