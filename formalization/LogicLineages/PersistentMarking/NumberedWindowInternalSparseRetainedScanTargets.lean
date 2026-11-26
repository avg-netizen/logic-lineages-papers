module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseDirectedSeen (scanGraph seenWitness)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- A member of the actual filtered output passed the original scan
against the fixed seen list at the same context and result type. -/
def ExactRetainedScan : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices seen ctx ty out k : OTerm α),
    Nonempty (Derivation body Γ ((passGraph E out vertices seen ctx ty ⊓ memberGraph out k).imp
      (scanGraph E seen ctx ty k)))

/-- Its predecessor is drawn from the unchanged seen list. The edge in
the original witness points from that predecessor to the retained k. -/
def ExactRetainedPredecessor : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices seen ctx ty out k : OTerm α),
    Nonempty (Derivation body Γ ((passGraph E out vertices seen ctx ty ⊓ memberGraph out k).imp
      (seenWitness E seen ctx ty k)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
