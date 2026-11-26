module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt allWindow)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowScalarAlgorithm (Settings)

/-- The same W supplied inside the actual directed edge guards every member
at every physical round index, starting with its guard on the original seed. -/
def ExactRoundsWindowFromRetained : Prop :=
  ExactRetainedPredecessor →
    ∀ (X : Program 2) (W : Program 3) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (ctx ty vertices seed fuel out : OTerm α),
      Nonempty (Derivation body Γ ((windowAt W ctx ty seed ⊓
        roundGraph (edge4 X W) out fuel vertices ctx ty seed).imp (allWindow W ctx ty out)))

/-- The same conclusion on the selected original cover and genuine length
fuel, even though no vertices, fuel or decoded list are supplied. -/
def ExactChosenMembersWindowFromRetained : Prop :=
  ExactRetainedPredecessor →
    ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
      (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed out : OTerm α),
      Nonempty (Derivation body Γ ((windowAt W ctx ty seed ⊓
        programGraph (membersAtSeed C X W s) out ![ctx,ty,seed]).imp (allWindow W ctx ty out)))

/-- A successful minimum from an admitted seed carries that same window
guard at the returned candidate. -/
def ExactSelectedWindowFromRetained : Prop :=
  ExactRetainedPredecessor →
    ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
      (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed k : OTerm α),
      Nonempty (Derivation body Γ ((windowAt W ctx ty seed ⊓ leastGraph C X W s ctx ty seed k).imp
        (windowAt W ctx ty k)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowTargets
