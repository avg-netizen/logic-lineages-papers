module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalLessThan (strictLess)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)

/-- A member of any actual round forces the initial seed to occur in the
original vertices. Both the fuel and the member are open object terms. -/
def ExactRoundSeedOrigin : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (fuel vertices ctx ty seed out k : OTerm α),
    Nonempty (Derivation body Γ ((roundGraph E out fuel vertices ctx ty seed ⊓ memberGraph out k).imp
      (memberGraph vertices seed)))

/-- A successful least call alone supplies both occurrence of the input seed
in its actual cover and the original internal order comparison. -/
def ExactSuccessfulSeedBound : Prop :=
  ExactRetainedPredecessor → ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed minimum : OTerm α),
    Nonempty (Derivation body Γ ((leastGraph C X W s ctx ty seed minimum).imp
      (occursInCover C s seed seed ⊓ (strictLess seed minimum).not)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginTargets
