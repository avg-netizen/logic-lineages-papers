module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersClosureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalLessThan (strictLess)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseScalarEdge (edge4)

/-- The real packed members output is closed under the guarded directed edge
whenever the destination occurs in the cover computed at the same seed. -/
def ExactPackedMembersClosure : Prop :=
  ExactRetainedPredecessor → ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty seed pool source target : OTerm α),
    let selected := programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓ memberGraph pool source
    let edge := acceptEdge (edge4 X W) ctx ty source target ⊓ occursInCover C s seed target
    Nonempty (Derivation body Γ ((selected ⊓ edge).imp (memberGraph pool target)))

/-- A successful original packed minimum has no smaller directed successor
in the same original seed cover. The computed pool is recovered internally. -/
def ExactMinimumEdgeBound : Prop :=
  ExactRetainedPredecessor → ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty seed minimum target : OTerm α),
    let edge := acceptEdge (edge4 X W) ctx ty minimum target ⊓ occursInCover C s seed target
    Nonempty (Derivation body Γ ((leastGraph C X W s ctx ty seed minimum ⊓ edge).imp
      (strictLess target minimum).not))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeTargets
